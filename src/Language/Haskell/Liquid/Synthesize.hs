module Language.Haskell.Liquid.Synthesize (
    synthesize
  ) where

import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.UX.Errors
import           Language.Haskell.Liquid.UX.CmdLine

import qualified Language.Fixpoint.Types as F

import qualified Data.HashMap.Strict as M 

synthesize :: M.HashMap F.Symbol SpecType -> SpecType -> String 
synthesize ctx t = mempty 