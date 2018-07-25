{-# LANGUAGE FlexibleContexts #-}

module Language.Haskell.Liquid.Bare.SymSort (
    txRefSort
  ) where

import qualified Data.HashMap.Strict                   as M
import           Prelude                               hiding (error)
import qualified GHC
import qualified Data.List                             as L
import           Data.Maybe                            (fromMaybe)
import           TyCon                                 (TyCon)
import           Language.Fixpoint.Misc                (fst3, snd3)
import           Language.Fixpoint.Types.Sorts
import           Language.Fixpoint.Types               (atLoc, meet, Reftable, Symbolic, Symbol)
import           Language.Haskell.Liquid.Types.RefType (appRTyCon, strengthen)
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.GHC.Misc      (fSrcSpan)
import           Language.Haskell.Liquid.Misc          (safeZipWithError)

import           Language.Haskell.Liquid.Bare.Types as Bare 
--  import           Language.Haskell.Liquid.Bare.Env

