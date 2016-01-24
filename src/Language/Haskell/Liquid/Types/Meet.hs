-- | This code has various wrappers around `meet` and `strengthen`
--   that are here so that we can throw decent error messages if
--   they fail. The module depends on `RefType` and `UX.Tidy`.

module Language.Haskell.Liquid.Types.Meet
     ( meetVarTypes ) where

import           Name
import qualified Language.Fixpoint.Types as F
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Types.Errors
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.UX.Tidy

meetVarTypes :: (PPrint v, NamedThing v)
             => v -> SpecType -> SpecType  -> SpecType
meetVarTypes v t1 t2 = meetError err t1 t2
  where
    err              = ErrMismatch (getSrcSpan v) (F.pprint v) d1 d2
    d1               = pprint (toRSort t1)
    d2               = pprint (toRSort t2)

meetError :: Error -> SpecType -> SpecType -> SpecType
meetError e t1 t2
  | meetable t1 t2   = t1 `F.meet` t2
  | otherwise        = panicError e
