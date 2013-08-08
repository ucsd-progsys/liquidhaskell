{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE BangPatterns              #-}

-- | This module contains all the code needed to output the result which 
--   is either: `SAFE` or `WARNING` with some reasonable error message when 
--   something goes wrong. All forms of errors/exceptions should go through 
--   here. The idea should be to report the error, the source position that 
--   causes it, generate a suitable .json file and then exit.

module Language.Haskell.Liquid.Result (

  -- * Final Result
    Result (..)

  -- * Different kinds of errors
  , Error (..)
  
  -- * Source information associated with each constraint
  , Cinfo (..)

  -- * Single Exit Function
  , exitWithResult
  ) where

import SrcLoc                                   (SrcSpan)
import qualified Language.Fixpoint.Types            as F
import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.GhcMisc          (pprDoc)
import Text.PrettyPrint.HughesPJ    
import Control.DeepSeq

------------------------------------------------------------------------
-- | Error Data Type ---------------------------------------------------
------------------------------------------------------------------------

data Result = Verified | Err [Error]

data Error  = 
    LiquidType  { pos :: !SrcSpan
                , act :: !SpecType
                , exp :: !SpecType
                , msg :: !String
                } -- ^ liquid type error

  | LiquidParse { pos :: !SrcSpan
                , msg :: !String
                } -- ^ specification parse error

  | LiquidSort  { pos :: !SrcSpan
                , msg :: !String
                } -- ^ sort error in specification

  | Ghc         { pos :: !SrcSpan
                , msg :: !String
                } -- ^ GHC error: parsing or type checking

instance Eq Error where 
  e1 == e2 = pos e1 == pos e2

instance Ord Error where 
  e1 <= e2 = pos e1 <= pos e2

------------------------------------------------------------------------
-- | Source Information Associated With Constraints --------------------
------------------------------------------------------------------------

data Cinfo    = Ci SrcSpan (Maybe Error) 
                deriving (Eq, Ord) 

instance PPrint Cinfo where
  pprint (Ci src e)  = pprDoc src <+> maybe empty pprint e

instance F.Fixpoint Cinfo where
  toFix = pprint

instance NFData Cinfo 

------------------------------------------------------------------------
-- | Converting Results To Answers -------------------------------------
------------------------------------------------------------------------

class IsResult a where
  result :: a -> Result

instance IsResult Error where
  result e = Err [e]

instance IsResult [Error] where
  result   = Err

------------------------------------------------------------------------
-- | Rendering Errors---------------------------------------------------
------------------------------------------------------------------------

instance PPrint Error where
  pprint = ppError

ppError :: Error -> Doc
ppError = pprDoc . pos

------------------------------------------------------------------------
-- | Exit Function -----------------------------------------------------
------------------------------------------------------------------------

exitWithResult = error "TODO: exitWithResult"


