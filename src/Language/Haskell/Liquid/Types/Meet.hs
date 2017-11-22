-- | This code has various wrappers around `meet` and `strengthen`
--   that are here so that we can throw decent error messages if
--   they fail. The module depends on `RefType` and `UX.Tidy`.

module Language.Haskell.Liquid.Types.Meet
     ( meetVarTypes ) where

import           SrcLoc
import           Text.PrettyPrint.HughesPJ (text, Doc)
import qualified Language.Fixpoint.Types as F
import           Language.Haskell.Liquid.Types

import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.UX.Tidy

meetVarTypes :: Doc -> (SrcSpan, SpecType) -> (SrcSpan, SpecType) -> SpecType
meetVarTypes v hs lq = meetError err hsT lqT
  where
    (hsSp, hsT)      = hs
    (lqSp, lqT)      = lq
    err              = ErrMismatch lqSp v (text "meetVarTypes") hsD lqD hsSp
    hsD              = F.pprint ({- toRSort -} hsT)
    lqD              = F.pprint ({- toRSort -} lqT)

meetError :: Error -> SpecType -> SpecType -> SpecType
meetError e t t'
  | meetable t t' = t `F.meet` t'
  | otherwise     = panicError e
