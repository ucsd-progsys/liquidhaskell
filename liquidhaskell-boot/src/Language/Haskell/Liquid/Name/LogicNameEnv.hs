module Language.Haskell.Liquid.Name.LogicNameEnv
  ( LogicNameEnv(..)
  , extendLogicNameEnv
  ) where

import qualified Liquid.GHC.API         as GHC
import           Language.Fixpoint.Types
import           Language.Haskell.Liquid.Types.Names


-- | For every symbol tells the corresponding LHName and Sort
--
-- Symbols are expected to have been created by 'lhNameToResolvedSymbol'.
--
data LogicNameEnv = LogicNameEnv
       { lneLHName :: SEnv LHName
         -- | Haskell names that have a reflected counterpart
       , lneReflected :: GHC.NameEnv LHName
       }

extendLogicNameEnv :: LogicNameEnv -> [LHName] -> LogicNameEnv
extendLogicNameEnv env ns =
    env
      { lneLHName =
          foldr (uncurry insertSEnv) (lneLHName env) [ (lhNameToResolvedSymbol n, n) | n <- ns]
      }
