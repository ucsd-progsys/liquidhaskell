{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE DeriveDataTypeable        #-}

module Language.Fixpoint.Errors (
  -- * Concrete Location Type
    SrcSpan (..)

  -- * Abstract Error Type
  , Error

  -- * Constructor
  , err

  -- * Accessors
  , errLoc
  , errMsg
  -- , errorInfo

  -- * Adding Insult to Injury
  , catMessage
  , catError

  -- * Fatal Exit
  , die

  ) where

import Text.PrettyPrint.HughesPJ
import Text.Parsec.Pos                   
import Data.Typeable
import Text.Printf 
import Control.Exception
import qualified Control.Monad.Error as E 
import Language.Fixpoint.PrettyPrint
import Language.Fixpoint.Types

-----------------------------------------------------------------------
-- | A Reusable SrcSpan Type ------------------------------------------
-----------------------------------------------------------------------

data SrcSpan = SS { sp_start :: !SourcePos, sp_stop :: !SourcePos} 
                 deriving (Eq, Ord, Show, Typeable)

instance PPrint SrcSpan where
  pprint = ppSrcSpan

ppSrcSpan z  = parens 
             $ text (printf "file %s: (%d, %d) - (%d, %d)" f l c l' c')  
  where 
    (f,l ,c )   = sourcePosElts $ sp_start z
    (_,l',c')   = sourcePosElts $ sp_stop  z

sourcePosElts s = (src, line, col)
  where 
    src         = sourceName   s 
    line        = sourceLine   s
    col         = sourceColumn s 

---------------------------------------------------------------------------
errorInfo :: Error -> (SrcSpan, String)
---------------------------------------------------------------------------
errorInfo (Error l msg) = (l, msg)


-----------------------------------------------------------------------
-- | A BareBones Error Type -------------------------------------------
-----------------------------------------------------------------------

data Error = Error { errLoc :: SrcSpan, errMsg :: String }
               deriving (Eq, Ord, Show, Typeable)

instance PPrint Error where
  pprint (Error l msg) = text $ printf "Error at %s\n  %s\n" (showpp l) msg 


instance Fixpoint Error where
  toFix = pprint

instance Exception Error

instance E.Error Error where
  strMsg = Error $ SS l l where l = initialPos ""


---------------------------------------------------------------------
catMessage :: Error -> String -> Error
---------------------------------------------------------------------
catMessage err msg = err {errMsg = msg ++ errMsg err} 

---------------------------------------------------------------------
catError :: Error -> Error -> Error
---------------------------------------------------------------------
catError e1 e2 = catMessage e1 $ show e2



---------------------------------------------------------------------
err :: SrcSpan -> String -> Error
---------------------------------------------------------------------
err = Error

---------------------------------------------------------------------
die :: Error -> a
---------------------------------------------------------------------
die = throw

