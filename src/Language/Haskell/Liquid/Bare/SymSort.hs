{-# LANGUAGE FlexibleContexts #-}

module Language.Haskell.Liquid.Bare.SymSort (
    txRefSort
  ) where

import Prelude hiding (error)

import qualified Data.List as L
import Data.Maybe              (fromMaybe)
import TyCon            (TyCon)
import Language.Fixpoint.Misc  (fst3, snd3)
import Language.Fixpoint.Types (srcSpan, atLoc, meet, TCEmb)

import Language.Haskell.Liquid.Types.RefType (appRTyCon, strengthen)
import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.GHC.Misc (fSrcSpan)
import Language.Haskell.Liquid.Misc (intToString, safeZipWithError)
import Language.Haskell.Liquid.Bare.Env
import Language.Haskell.Liquid.Types.Errors (panic)

-- EFFECTS: TODO is this the SAME as addTyConInfo? No. `txRefSort`
-- (1) adds the _real_ sorts to RProp,
-- (2) gathers _extra_ RProp at turnst them into refinements,
--     e.g. tests/pos/multi-pred-app-00.hs

txRefSort :: TCEnv -> TCEmb TyCon -> Located SpecType -> Located SpecType
txRefSort tyi tce t = atLoc t $ mapBot (addSymSort (fSrcSpan t) tce tyi) (val t)

addSymSort sp tce tyi (RApp rc@(RTyCon _ _ _) ts rs r)
  = RApp rc ts (zipWith3 (addSymSortRef sp rc) pvs rargs [1..]) r'
  where
    rc'                = appRTyCon tce tyi rc ts
    pvs                = rTyConPVs rc'
    (rargs, rrest)     = splitAt (length pvs) rs
    r'                 = L.foldl' go r rrest
    go r (RProp _ (RHole r')) = r' `meet` r
    go r (RProp  _ t' )       = let r' = fromMaybe mempty (stripRTypeBase t') in r `meet` r'

addSymSort _ _ _ t
  = t

addSymSortRef sp rc p r i
  | isPropPV p
  = addSymSortRef' sp rc i p r
  | otherwise
  = panic Nothing "addSymSortRef: malformed ref application"

addSymSortRef' _ _ _ p (RProp s (RVar v r)) | isDummy v
  = RProp xs t
    where
      t  = ofRSort (pvType p) `strengthen` r
      xs = spliceArgs "addSymSortRef 1" s p

addSymSortRef' sp rc i p (RProp _ (RHole r@(MkUReft _ (Pr [up]) _)))
  | length xs == length ts
  = RProp xts (RHole r)
  | otherwise
  = uError $ ErrPartPred sp (pprint rc) (pprint $ pname up) i (length xs) (length ts)
    where
      xts = safeZipWithError "addSymSortRef'" xs ts
      xs  = snd3 <$> pargs up
      ts  = fst3 <$> pargs p

addSymSortRef' _ _ _ _ (RProp s (RHole r))
  = RProp s (RHole r)

addSymSortRef' _ _ _ p (RProp s t)
  = RProp xs t
    where
      xs = spliceArgs "addSymSortRef 2" s p

spliceArgs msg s p = go (fst <$> s) (pargs p)
  where
    go []     []           = []
    go []     ((s,x,_):as) = (x, s):go [] as
    go (x:xs) ((s,_,_):as) = (x,s):go xs as
    go xs     []           = panic Nothing $ "spliceArgs: " ++ msg ++ "on XS=" ++ show xs
