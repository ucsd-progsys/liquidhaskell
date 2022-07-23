-- | This code has various wrappers around `meet` and `strengthen`
--   that are here so that we can throw decent error messages if
--   they fail. The module depends on `RefType` and `UX.Tidy`.

module Language.Haskell.Liquid.Types.Meet ( meetVarTypes ) where

import           Text.PrettyPrint.HughesPJ (Doc)
import qualified Language.Fixpoint.Types as F
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.Types.RefType ()
import           Liquid.GHC.API as Ghc

meetVarTypes :: F.TCEmb TyCon -> Doc -> (SrcSpan, SpecType) -> (SrcSpan, SpecType) -> SpecType
meetVarTypes _emb _v hs lq = {- meetError emb err -} F.meet hsT lqT
  where
    (_hsSp, hsT)      = hs
    (_lqSp, lqT)      = lq
    -- _err              = ErrMismatch lqSp v (text "meetVarTypes") hsD lqD hsSp
    -- _hsD              = F.pprint hsT
    -- _lqD              = F.pprint lqT
{- 
  
_meetError :: F.TCEmb TyCon -> Error -> SpecType -> SpecType -> SpecType
_meetError _emb _e t t'
  -- // | meetable emb t t'
  | True              = t `F.meet` t'
  -- // | otherwise         = panicError e

_meetable :: F.TCEmb TyCon -> SpecType -> SpecType -> Bool
_meetable _emb t1 t2 = F.notracepp ("meetable: " ++  showpp (s1, t1, s2, t2)) (s1 == s2)
  where
    s1              = tx t1
    s2              = tx t2
    tx              = rTypeSort _emb . toRSort

-}
