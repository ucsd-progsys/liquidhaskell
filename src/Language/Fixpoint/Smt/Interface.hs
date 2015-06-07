{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE PatternGuards             #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE UndecidableInstances      #-}

-- | This module contains an SMTLIB2 interface for
--   1. checking the validity, and,
--   2. computing satisfying assignments
--   for formulas.
--   By implementing a binary interface over the SMTLIB2 format defined at
--   http://www.smt-lib.org/
--   http://www.grammatech.com/resource/smt/SMTLIBTutorial.pdf

module Language.Fixpoint.Smt.Interface (

    -- * Commands
      Command  (..)

    -- * Responses
    , Response (..)

    -- * Typeclass for SMTLIB2 conversion
    , SMTLIB2 (..)

    -- * Creating and killing SMTLIB2 Process
    , Context (..)
    , makeContext
    , makeContextNoLog
    , cleanupContext

    -- * Execute Queries
    , command
    , smtWrite

    -- * Query API
    , smtDecl
    , smtAssert
    , smtCheckUnsat
    , smtBracket
    , smtDistinct

    -- * Theory Symbols
    , theorySymbols
      -- smt_set_funs

    ) where

import           Language.Fixpoint.Config (SMTSolver (..))
import           Language.Fixpoint.Errors
import           Language.Fixpoint.Files
import           Language.Fixpoint.Types
import           Language.Fixpoint.Smt.Types
import           Language.Fixpoint.Smt.Theories
import           Language.Fixpoint.Smt.Serialize



import           Control.Applicative      ((*>), (<$>), (<*), (<|>))
import           Control.Monad
import           Data.Char
import qualified Data.HashMap.Strict      as M
import qualified Data.List                as L
import           Data.Monoid
import qualified Data.Text                as T
import           Data.Text.Format
import qualified Data.Text.IO             as TIO
import qualified Data.Text.Lazy           as LT
import qualified Data.Text.Lazy.IO        as LTIO
import           System.Directory
import           System.Exit              hiding (die)
import           System.FilePath
import           System.IO                (Handle, IOMode (..), hClose, hFlush,
                                           openFile)
import           System.Process
import qualified Data.Attoparsec.Text     as A

{- Usage:
runFile f
  = readFile f >>= runString

runString str
  = runCommands $ rr str

runCommands cmds
  = do me   <- makeContext Z3
       mapM_ (T.putStrLn . smt2) cmds
       zs   <- mapM (command me) cmds
       return zs
-}

--------------------------------------------------------------------------
-- | SMT IO --------------------------------------------------------------
--------------------------------------------------------------------------

--------------------------------------------------------------------------
command              :: Context -> Command -> IO Response
--------------------------------------------------------------------------
command me !cmd      = {-# SCC "command" #-} say me cmd >> hear me cmd
  where
    say me               = smtWrite me . smt2
    hear me CheckSat     = smtRead me
    hear me (GetValue _) = smtRead me
    hear me _            = return Ok



smtWrite :: Context -> LT.Text -> IO ()
smtWrite me !s = smtWriteRaw me s

smtRead :: Context -> IO Response
smtRead me = {-# SCC "smtRead" #-}
    do ln  <- smtReadRaw me
       res <- A.parseWith (smtReadRaw me) responseP ln
       case A.eitherResult res of
         Left e  -> error e
         Right r -> do
           maybe (return ()) (\h -> hPutStrLnNow h $ format "; SMT Says: {}" (Only $ show r)) (cLog me)
           when (verbose me) $
             LTIO.putStrLn $ format "SMT Says: {}" (Only $ show r)
           return r

responseP = {-# SCC "responseP" #-} A.char '(' *> sexpP
         <|> A.string "sat"     *> return Sat
         <|> A.string "unsat"   *> return Unsat
         <|> A.string "unknown" *> return Unknown

sexpP = {-# SCC "sexpP" #-} A.string "error" *> (Error <$> errorP)
     <|> Values <$> valuesP

errorP = A.skipSpace *> A.char '"' *> A.takeWhile1 (/='"') <* A.string "\")"

valuesP = A.many1' pairP <* (A.char ')')

pairP = {-# SCC "pairP" #-}
  do A.skipSpace
     A.char '('
     !x <- symbolP
     A.skipSpace
     !v <- valueP
     A.char ')'
     return (x,v)

symbolP = {-# SCC "symbolP" #-} symbol <$> A.takeWhile1 (not . isSpace)

valueP = {-# SCC "valueP" #-} negativeP
      <|> A.takeWhile1 (\c -> not (c == ')' || isSpace c))

negativeP
  = do v <- A.char '(' *> A.takeWhile1 (/=')') <* A.char ')'
       return $ "(" <> v <> ")"

{-@ pairs :: {v:[a] | (len v) mod 2 = 0} -> [(a,a)] @-}
pairs :: [a] -> [(a,a)]
pairs !xs = case L.splitAt 2 xs of
              ([],b)      -> []
              ([x,y], zs) -> (x,y) : pairs zs

smtWriteRaw      :: Context -> LT.Text -> IO ()
smtWriteRaw me !s = {-# SCC "smtWriteRaw" #-} do
  hPutStrLnNow (cOut me) s
  maybe (return ()) (`hPutStrLnNow` s) (cLog me)

smtReadRaw       :: Context -> IO Raw
smtReadRaw me    = {-# SCC "smtReadRaw" #-} TIO.hGetLine (cIn me)

hPutStrLnNow h !s   = LTIO.hPutStrLn h s >> hFlush h

--------------------------------------------------------------------------
-- | SMT Context ---------------------------------------------------------
--------------------------------------------------------------------------

--------------------------------------------------------------------------
makeContext   :: SMTSolver -> FilePath -> IO Context
--------------------------------------------------------------------------
makeContext s f
  = do me  <- makeProcess s
       pre <- smtPreamble s me
       createDirectoryIfMissing True $ takeDirectory smtFile
       hLog               <- openFile smtFile WriteMode
       let me' = me { cLog = Just hLog }
       mapM_ (smtWrite me') pre
       return me'
    where
       smtFile = extFileName Smt2 f


makeContextNoLog s
  = do me  <- makeProcess s
       pre <- smtPreamble s me
       mapM_ (smtWrite me) pre
       return me

makeProcess s
  = do (hOut, hIn, _ ,pid) <- runInteractiveCommand $ smtCmd s
       return $ Ctx pid hIn hOut Nothing False

--------------------------------------------------------------------------
cleanupContext :: Context -> IO ExitCode
--------------------------------------------------------------------------
cleanupContext me@(Ctx {..})
  = do smtWrite me "(exit)"
       code <- waitForProcess pId
       hClose cIn
       hClose cOut
       maybe (return ()) hClose cLog
       return code

{- "z3 -smt2 -in"                   -}
{- "z3 -smtc SOFT_TIMEOUT=1000 -in" -}
{- "z3 -smtc -in MBQI=false"        -}

smtCmd Z3      = "z3 -smt2 -in"
smtCmd Mathsat = "mathsat -input=smt2"
smtCmd Cvc4    = "cvc4 --incremental -L smtlib2"

-- DON'T REMOVE THIS! z3 changed the names of options between 4.3.1 and 4.3.2...
smtPreamble Z3 me
  = do smtWrite me "(get-info :version)"
       r <- (!!1) . T.splitOn "\"" <$> smtReadRaw me
       case T.words r of
         "4.3.2" : _  -> return $ z3_432_options ++ z3Preamble
         _            -> return $ z3_options     ++ z3Preamble
smtPreamble _  _
  = return smtlibPreamble

-----------------------------------------------------------------------------
-- | SMT Commands -----------------------------------------------------------
-----------------------------------------------------------------------------

smtPush, smtPop   :: Context -> IO ()
smtPush me        = interact' me Push
smtPop me         = interact' me Pop


smtDecl :: Context -> Symbol -> Sort -> IO ()
smtDecl me x t = interact' me (Declare x ins out)
  where
    (ins, out) = deconSort t

deconSort :: Sort -> ([Sort], Sort)
deconSort t = case functionSort t of
                Just (_, ins, out) -> (ins, out)
                Nothing            -> ([] , t  )

smtAssert :: Context -> Pred -> IO ()
smtAssert me p    = interact' me (Assert Nothing p)

smtDistinct :: Context -> [Expr] -> IO ()
smtDistinct me az = interact' me (Distinct az)

smtCheckUnsat :: Context -> IO Bool
smtCheckUnsat me  = respSat <$> command me CheckSat

smtBracket :: Context -> IO a -> IO a
smtBracket me a   = do smtPush me
                       r <- a
                       smtPop me
                       return r

respSat Unsat   = True
respSat Sat     = False
respSat Unknown = False
respSat r       = die $ err dummySpan $ "crash: SMTLIB2 respSat = " ++ show r

interact' me cmd  = void $ command me cmd

-- DON'T REMOVE THIS! z3 changed the names of options between 4.3.1 and 4.3.2...
z3_432_options
  = [ "(set-option :auto-config false)"
    , "(set-option :model true)"
    , "(set-option :model.partial false)"
    , "(set-option :smt.mbqi false)" ]

z3_options
  = [ "(set-option :auto-config false)"
    , "(set-option :model true)"
    , "(set-option :model-partial false)"
    , "(set-option :mbqi false)" ]

