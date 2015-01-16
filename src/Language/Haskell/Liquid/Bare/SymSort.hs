module Language.Haskell.Liquid.Bare.SymSort (
    txRefSort
  ) where

import Control.Applicative ((<$>))

import qualified Data.List as L

import Language.Fixpoint.Misc (errorstar, safeZip, fst3, snd3)
import Language.Fixpoint.Types (meet)

import Language.Haskell.Liquid.RefType (appRTyCon, strengthen)
import Language.Haskell.Liquid.Types

-- TODO: Rename, "Sort" isn't a good name for this module

-- EFFECTS: TODO is this the SAME as addTyConInfo? No. `txRefSort`
-- (1) adds the _real_ sorts to RProp,
-- (2) gathers _extra_ RProp at turnst them into refinements,
--     e.g. tests/pos/multi-pred-app-00.hs
txRefSort tyi tce = mapBot (addSymSort tce tyi)

addSymSort tce tyi (RApp rc@(RTyCon _ _ _) ts rs r) 
  = RApp rc ts (zipWith addSymSortRef pvs rargs) r'
  where
    rc'                = appRTyCon tce tyi rc ts
    pvs                = rTyConPVs rc' 
    (rargs, rrest)     = splitAt (length pvs) rs
    r'                 = L.foldl' go r rrest
    go r (RPropP _ r') = r' `meet` r
    go _ (RHProp _ _ ) = errorstar "TODO:EFFECTS:addSymSort"
    go _ _             = errorstar "YUCKER" -- r

addSymSort _ _ t 
  = t

addSymSortRef _ (RHProp _ _)   = errorstar "TODO:EFFECTS:addSymSortRef"
addSymSortRef p r | isPropPV p = addSymSortRef' p r 
                  | otherwise  = errorstar "addSymSortRef: malformed ref application"


addSymSortRef' p (RProp s (RVar v r)) | isDummy v
  = RProp xs t
    where
      t  = ofRSort (pvType p) `strengthen` r
      xs = spliceArgs "addSymSortRef 1" s p

addSymSortRef' p (RProp s t) 
  = RProp xs t
    where
      xs = spliceArgs "addSymSortRef 2" s p

-- EFFECTS: why can't we replace the next two equations with (breaks many tests)
--
-- EFFECTS: addSymSortRef' (PV _ (PVProp t) _ ptxs) (RPropP s r@(U _ (Pr [up]) _)) 
-- EFFECTS:   = RProp xts $ (ofRSort t) `strengthen` r
-- EFFECTS:     where
-- EFFECTS:       xts = safeZip "addRefSortMono" xs ts
-- EFFECTS:       xs  = snd3 <$> pargs up
-- EFFECTS:       ts  = fst3 <$> ptxs
--    
-- EFFECTS: addSymSortRef' (PV _ (PVProp t) _ _) (RPropP s r)
-- EFFECTS:   = RProp s $ (ofRSort t) `strengthen` r

addSymSortRef' p (RPropP _ r@(U _ (Pr [up]) _)) 
  = RProp xts ((ofRSort $ pvType p) `strengthen` r)
    where
      xts = safeZip "addRefSortMono" xs ts
      xs  = snd3 <$> pargs up
      ts  = fst3 <$> pargs p

addSymSortRef' _ (RPropP s r)
  = RPropP s r

addSymSortRef' _ _
  = errorstar "TODO:EFFECTS:addSymSortRef'"

spliceArgs msg s p = safeZip msg (fst <$> s) (fst3 <$> pargs p) 

