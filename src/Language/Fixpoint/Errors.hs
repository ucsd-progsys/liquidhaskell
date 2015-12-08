{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
module Language.Fixpoint.Errors (
  -- * Concrete Location Type
    SrcSpan (..)
  , dummySpan
  , sourcePosElts

  -- * Abstract Error Type
  , Error

  -- * Constructor
  , err

  -- * Accessors
  , errLoc
  , errMsg
  , result

  -- * Adding Insult to Injury
  , catMessage
  , catError
  , catErrors

  -- * Fatal Exit
  , die
  , exit

  -- * Some popular errors
  , errFreeVarInQual
  ) where

import           Control.Exception
import qualified Control.Monad.Error           as E
import           Data.Generics                 (Data)
import           Data.Hashable
import           Data.Typeable
import           GHC.Generics                  (Generic)
import           Language.Fixpoint.PrettyPrint
import           Language.Fixpoint.Types
import           Language.Fixpoint.Misc
import           Text.Parsec.Pos
import           Text.PrettyPrint.HughesPJ
import           Text.Printf

-----------------------------------------------------------------------
-- | A Reusable SrcSpan Type ------------------------------------------
-----------------------------------------------------------------------

data SrcSpan = SS { sp_start :: !SourcePos
                  , sp_stop  :: !SourcePos}
                 deriving (Eq, Ord, Show, Data, Typeable, Generic)

instance PPrint SrcSpan where
  pprint = ppSrcSpan

-- ppSrcSpan_short z = parens
--                   $ text (printf "file %s: (%d, %d) - (%d, %d)" (takeFileName f) l c l' c')
--   where
--     (f,l ,c )     = sourcePosElts $ sp_start z
--     (_,l',c')     = sourcePosElts $ sp_stop  z


ppSrcSpan z       = text (printf "%s:%d:%d-%d:%d" f l c l' c')
                -- parens $ text (printf "file %s: (%d, %d) - (%d, %d)" (takeFileName f) l c l' c')
  where
    (f,l ,c )     = sourcePosElts $ sp_start z
    (_,l',c')     = sourcePosElts $ sp_stop  z

sourcePosElts s = (src, line, col)
  where
    src         = sourceName   s
    line        = sourceLine   s
    col         = sourceColumn s

instance Hashable SourcePos where
  hashWithSalt i   = hashWithSalt i . sourcePosElts

instance Hashable SrcSpan where
  hashWithSalt i z = hashWithSalt i (sp_start z, sp_stop z)



---------------------------------------------------------------------------
-- errorInfo :: Error -> (SrcSpan, String)
-- ------------------------------------------------------------------------
-- errorInfo (Error l msg) = (l, msg)


-----------------------------------------------------------------------
-- | A BareBones Error Type -------------------------------------------
-----------------------------------------------------------------------

data Error = Error { errLoc :: SrcSpan, errMsg :: String }
               deriving (Eq, Ord, Show, Data, Typeable, Generic)

instance PPrint Error where
  pprint (Error l msg) = ppSrcSpan l <> text (": Error: " ++ msg)
                         -- text $ printf "%s\n  %s\n" (showpp l) msg

instance Fixpoint Error where
  toFix = pprint

instance Exception Error
instance Exception (FixResult Error)

instance E.Error Error where
  strMsg = Error dummySpan

dummySpan = SS l l
  where l = initialPos ""

---------------------------------------------------------------------
catMessage :: Error -> String -> Error
---------------------------------------------------------------------
catMessage e msg = e {errMsg = msg ++ errMsg e}

---------------------------------------------------------------------
catError :: Error -> Error -> Error
---------------------------------------------------------------------
catError e1 e2 = catMessage e1 $ show e2

---------------------------------------------------------------------
catErrors :: ListNE Error -> Error
---------------------------------------------------------------------
catErrors = foldr1 catError


---------------------------------------------------------------------
err :: SrcSpan -> String -> Error
---------------------------------------------------------------------
err = Error

---------------------------------------------------------------------
die :: Error -> a
---------------------------------------------------------------------
die = throw

---------------------------------------------------------------------
result :: Error -> Result a
---------------------------------------------------------------------
result e = Result (Crash [] msg) mempty
  where
    msg  = showpp e

---------------------------------------------------------------------
exit :: a -> IO a -> IO a
---------------------------------------------------------------------
exit def act = catch act $ \(e :: Error) -> do
  putStrLn $ "Unexpected Error: " ++ showpp e
  return def


---------------------------------------------------------------------
-- | Catalogue of Errors --------------------------------------------
---------------------------------------------------------------------

errFreeVarInQual  :: Qualifier -> Error
errFreeVarInQual q = err sp $ printf "Qualifier with free vars : %s \n" (showFix q)
  where
    sp             = SS l l
    l              = q_pos q
