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
  -- * Single Exit Function
   exitWithResult
  ) where

import SrcLoc                                   (SrcSpan)
import qualified Language.Fixpoint.Types            as F
import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.GhcMisc          (pprDoc)
import Text.PrettyPrint.HughesPJ    
import Control.DeepSeq
import Data.List                                (sortBy)
import Data.Function                            (on)

------------------------------------------------------------------------
-- | Exit Function -----------------------------------------------------
------------------------------------------------------------------------

exitWithResult = error "TOBD: exitWithResult"

instance F.Fixpoint (F.FixResult Cinfo) where
  toFix F.Safe           = text "Safe"
  toFix F.UnknownError   = text "Unknown Error!"
  toFix (F.Crash xs msg) = vcat $ text "Crash!"  : pprCinfos "CRASH:   " xs ++ [parens (text msg)] 
  toFix (F.Unsafe xs)    = vcat $ text "Unsafe:" : pprCinfos "WARNING: " xs

pprCinfos     :: String -> [Cinfo] -> [Doc] 
pprCinfos msg = map ((text msg <+>) . F.toFix) . sortBy (compare `on` ci_loc) 

------------------------------------------------------------------------
-- | Rendering Errors---------------------------------------------------
------------------------------------------------------------------------

instance PPrint Cinfo where
  pprint (Ci src e)  = pprDoc src <+> maybe empty pprint e

instance F.Fixpoint Cinfo where
  toFix = pprint

instance PPrint Error where
  pprint = ppError

ppError :: Error -> Doc
ppError = error "TOBD: ppError" -- pprDoc . pos

