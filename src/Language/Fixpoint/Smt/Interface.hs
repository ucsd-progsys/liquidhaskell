{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings         #-}
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
    , makeContextWithSEnv
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
    -- , theorySymbols
      -- smt_set_funs

    -- * Check Validity
    , checkValid, checkValidWithContext
    , checkValids
    , makeZ3Context

    ) where

import           Language.Fixpoint.Types.Config (SMTSolver (..))
import           Language.Fixpoint.Misc   (errorstar)
import           Language.Fixpoint.Types.Errors
import           Language.Fixpoint.Utils.Files
import           Language.Fixpoint.Types
import           Language.Fixpoint.Smt.Types
import           Language.Fixpoint.Smt.Theories  (preamble)
import           Language.Fixpoint.Smt.Serialize (initSMTEnv)



import           Control.Applicative      ((<|>))
import           Control.Monad
import           Data.Char
import           Data.Monoid
import qualified Data.Text                as T
import           Data.Text.Format         hiding (format)
import qualified Data.Text.IO             as TIO
-- import qualified Data.Text.Lazy           as LT
-- import qualified Data.Text.Lazy.IO        as LTIO
import           System.Directory
import           System.Console.CmdArgs.Verbosity
import           System.Exit              hiding (die)
import           System.FilePath
import           System.IO                (IOMode (..), hClose, hFlush, openFile)
import           System.Process
import qualified Data.Attoparsec.Text     as A

{-
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


-- TODO take makeContext's Bool from caller instead of always using False?
makeZ3Context :: FilePath -> [(Symbol, Sort)] -> IO Context
makeZ3Context f xts
  = do me <- makeContext False Z3 f
       smtDecls me xts
       return me

checkValidWithContext :: Context -> [(Symbol, Sort)] -> Expr -> Expr -> IO Bool
checkValidWithContext me xts p q
  = smtBracket me $ do smtDecls me xts
                       smtAssert me $ pAnd [p, PNot q]
                       smtCheckUnsat me


-- | type ClosedPred E = {v:Pred | subset (vars v) (keys E) }
-- checkValid :: e:Env -> ClosedPred e -> ClosedPred e -> IO Bool
checkValid :: Bool -> FilePath -> [(Symbol, Sort)] -> Expr -> Expr -> IO Bool
checkValid u f xts p q
  = do me <- makeContext u Z3 f
       smtDecls me xts
       smtAssert me $ pAnd [p, PNot q]
       smtCheckUnsat me

-- | If you already HAVE a context, where all the variables have declared types
--   (e.g. if you want to make MANY repeated Queries)

-- checkValid :: e:Env -> [ClosedPred e] -> IO [Bool]
checkValids :: Bool -> FilePath -> [(Symbol, Sort)] -> [Expr] -> IO [Bool]
checkValids u f xts ps
  = do me <- makeContext u Z3 f
       smtDecls me xts
       forM ps $ \p ->
          smtBracket me $
            smtAssert me (PNot p) >> smtCheckUnsat me

-- debugFile :: FilePath
-- debugFile = "DEBUG.smt2"

--------------------------------------------------------------------------
-- | SMT IO --------------------------------------------------------------
--------------------------------------------------------------------------


--------------------------------------------------------------------------
command              :: Context -> Command -> IO Response
--------------------------------------------------------------------------
command me !cmd      = {-# SCC "command" #-} say cmd >> hear cmd
  where
    say               = smtWrite me . smt2 (smtenv me)
    hear CheckSat     = smtRead me
    hear (GetValue _) = smtRead me
    hear _            = return Ok


smtWrite :: Context -> T.Text -> IO ()
smtWrite me !s = smtWriteRaw me s

smtRead :: Context -> IO Response
smtRead me = {-# SCC "smtRead" #-}
    do ln  <- smtReadRaw me
       res <- A.parseWith (smtReadRaw me) responseP ln
       case A.eitherResult res of
         Left e  -> errorstar $ "SMTREAD:" ++ e
         Right r -> do
           maybe (return ()) (\h -> hPutStrLnNow h $ format "; SMT Says: {}" (Only $ show r)) (cLog me)
           -- when (verbose me) $ TIO.putStrLn $ format "SMT Says: {}" (Only $ show r)
           return r

responseP = {-# SCC "responseP" #-} A.char '(' *> sexpP
         <|> A.string "sat"     *> return Sat
         <|> A.string "unsat"   *> return Unsat
         <|> A.string "unknown" *> return Unknown

sexpP = {-# SCC "sexpP" #-} A.string "error" *> (Error <$> errorP)
     <|> Values <$> valuesP

errorP = A.skipSpace *> A.char '"' *> A.takeWhile1 (/='"') <* A.string "\")"

valuesP = A.many1' pairP <* A.char ')'

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

-- {- pairs :: {v:[a] | (len v) mod 2 = 0} -> [(a,a)] -}
-- pairs :: [a] -> [(a,a)]
-- pairs !xs = case L.splitAt 2 xs of
--              ([],_)      -> []
--              ([x,y], zs) -> (x,y) : pairs zs

smtWriteRaw      :: Context -> T.Text -> IO ()
smtWriteRaw me !s = {-# SCC "smtWriteRaw" #-} do
  hPutStrLnNow (cOut me) s
  -- whenLoud $ TIO.appendFile debugFile (s <> "\n")
  maybe (return ()) (`hPutStrLnNow` s) (cLog me)

smtReadRaw       :: Context -> IO Raw
smtReadRaw me    = {-# SCC "smtReadRaw" #-} TIO.hGetLine (cIn me)

hPutStrLnNow h !s   = TIO.hPutStrLn h s >> hFlush h

--------------------------------------------------------------------------
-- | SMT Context ---------------------------------------------------------
--------------------------------------------------------------------------

--------------------------------------------------------------------------
makeContext   :: Bool -> SMTSolver -> FilePath -> IO Context
--------------------------------------------------------------------------
makeContext u s f
  = do me   <- makeProcess s
       pre  <- smtPreamble u s me
       createDirectoryIfMissing True $ takeDirectory smtFile
       hLog <- openFile smtFile WriteMode
       let me' = me { cLog = Just hLog }
       mapM_ (smtWrite me') pre
       return me'
    where
       smtFile = extFileName Smt2 f

makeContextWithSEnv :: Bool -> SMTSolver -> FilePath  -> SMTEnv -> IO Context 
makeContextWithSEnv u s f env 
  = (\cxt -> cxt {smtenv = env}) <$> makeContext u s f

makeContextNoLog :: Bool -> SMTSolver -> IO Context
makeContextNoLog u s
  = do me  <- makeProcess s
       pre <- smtPreamble u s me
       mapM_ (smtWrite me) pre
       return me

makeProcess :: SMTSolver -> IO Context
makeProcess s
  = do (hOut, hIn, _ ,pid) <- runInteractiveCommand $ smtCmd s
       loud <- isLoud
       return Ctx { pId     = pid
                  , cIn     = hIn
                  , cOut    = hOut
                  , cLog    = Nothing
                  , verbose = loud
                  , smtenv  = initSMTEnv }

--------------------------------------------------------------------------
cleanupContext :: Context -> IO ExitCode
--------------------------------------------------------------------------
cleanupContext (Ctx {..})
  = do hClose cIn
       hClose cOut
       maybe (return ()) hClose cLog
       waitForProcess pId

{- "z3 -smt2 -in"                   -}
{- "z3 -smtc SOFT_TIMEOUT=1000 -in" -}
{- "z3 -smtc -in MBQI=false"        -}

smtCmd Z3      = "z3 -smt2 -in"
smtCmd Mathsat = "mathsat -input=smt2"
smtCmd Cvc4    = "cvc4 --incremental -L smtlib2"

-- DON'T REMOVE THIS! z3 changed the names of options between 4.3.1 and 4.3.2...
smtPreamble u Z3 me
  = do smtWrite me "(get-info :version)"
       v:_ <- T.words . (!!1) . T.splitOn "\"" <$> smtReadRaw me
       if T.splitOn "." v `versionGreater` ["4", "3", "2"]
         then return $ z3_432_options ++ preamble u Z3
         else return $ z3_options     ++ preamble u Z3
smtPreamble u s _
  = return $ preamble u s

versionGreater (x:xs) (y:ys)
  | x >  y = True
  | x == y = versionGreater xs ys
  | x <  y = False
versionGreater _  [] = True
versionGreater [] _  = False
versionGreater _ _ = errorstar "Interface.versionGreater called with bad arguments"

-----------------------------------------------------------------------------
-- | SMT Commands -----------------------------------------------------------
-----------------------------------------------------------------------------

smtPush, smtPop   :: Context -> IO ()
smtPush me        = interact' me Push
smtPop me         = interact' me Pop


smtDecls :: Context -> [(Symbol, Sort)] -> IO ()
smtDecls me xts = forM_ xts (\(x,t) -> smtDecl me x t)

smtDecl :: Context -> Symbol -> Sort -> IO ()
smtDecl me x t = interact' me (Declare x ins out)
  where
    (ins, out) = deconSort t

deconSort :: Sort -> ([Sort], Sort)
deconSort t = case functionSort t of
                Just (_, ins, out) -> (ins, out)
                Nothing            -> ([] , t  )

smtAssert :: Context -> Expr -> IO ()
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
