{-# LANGUAGE FlexibleContexts #-}

module Language.Haskell.Liquid.Bare.SymSort (
    txRefSort
  ) where

import Prelude hiding (error)

import qualified Data.List as L
import Data.Maybe              (fromMaybe)


import Language.Fixpoint.Misc  (fst3, snd3)
import Language.Fixpoint.Types (meet)

import Language.Haskell.Liquid.Types.RefType (appRTyCon, strengthen)
import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.Misc (safeZipWithError)

import Language.Haskell.Liquid.Types.Errors (panic)

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
    go r (RProp  _ t' )       = let r' = fromMaybe mempty (stripRTypeBase t') in r `meet` r'

addSymSort _ _ t
  = t


addSymSortRef rc p r i | isPropPV p = addSymSortRef' rc i p r
                       | otherwise  = panic Nothing "addSymSortRef: malformed ref application"
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

spliceArgs msg s p = go (fst <$> s) (pargs p)
  where
    go []     []           = [] 
    go []     ((s,x,_):as) = (x, s):go [] as
    go (x:xs) ((s,_,_):as) = (x,s):go xs as
    go xs     []           = panic Nothing $ "spliceArgs: " ++ msg ++ "on XS=" ++ show xs 

intToString 1 = "1st"
intToString 2 = "2nd"
intToString 3 = "3rd"
intToString n = show n ++ "th"
