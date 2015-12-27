module Language.Haskell.Liquid.Bare.SymSort (
    txRefSort
  ) where

import Control.Applicative ((<$>))

import qualified Data.List as L

import Language.Fixpoint.Misc (errorstar, safeZip, fst3, snd3)
import Language.Fixpoint.Types (meet)

import Language.Haskell.Liquid.Types.RefType (appRTyCon, strengthen)
import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.Misc (safeZipWithError)

-- EFFECTS: TODO is this the SAME as addTyConInfo? No. `txRefSort`
-- (1) adds the _real_ sorts to RProp,
-- (2) gathers _extra_ RProp at turnst them into refinements,
--     e.g. tests/pos/multi-pred-app-00.hs
txRefSort tyi tce = mapBot (addSymSort tce tyi)

addSymSort tce tyi (RApp rc@(RTyCon _ _ _) ts rs r)
  = RApp rc ts (zipWith3 (addSymSortRef rc) pvs rargs [1..]) r'
  where
    rc'                = appRTyCon tce tyi rc ts
    pvs                = rTyConPVs rc'
    (rargs, rrest)     = splitAt (length pvs) rs
    r'                 = L.foldl' go r rrest
    go r (RProp _ (RHole r')) = r' `meet` r
    go r (RProp  _ _ ) = r -- is this correct?

addSymSort _ _ t
  = t


addSymSortRef rc p r i | isPropPV p = addSymSortRef' rc i p r
                       | otherwise  = errorstar "addSymSortRef: malformed ref application"
addSymSortRef' _ _ p (RProp s (RVar v r)) | isDummy v
  = RProp xs t
    where
      t  = ofRSort (pvType p) `strengthen` r
      xs = spliceArgs "addSymSortRef 1" s p
addSymSortRef' rc i p (RProp _ (RHole r@(MkUReft _ (Pr [up]) _)))
  = RProp xts (RHole r) -- (ofRSort (pvType p) `strengthen` r)
    where
      xts = safeZipWithError msg xs ts
      xs  = snd3 <$> pargs up
      ts  = fst3 <$> pargs p
      msg = intToString i ++ " argument of " ++ show rc ++ " is " ++ show (pname up)
            ++ " that expects " ++ show (length ts) ++ " arguments, but it has " ++ show (length xs)
addSymSortRef' _ _ _ (RProp s (RHole r))
  = RProp s (RHole r) -- (ofRSort (pvType p) `strengthen` r)
addSymSortRef' _ _ p (RProp s t)
  = RProp xs t
    where
      xs = spliceArgs "addSymSortRef 2" s p

spliceArgs msg s p = safeZip msg (fst <$> s) (fst3 <$> pargs p)

intToString 1 = "1st"
intToString 2 = "2nd"
intToString 3 = "3rd"
intToString n = show n ++ "th"
