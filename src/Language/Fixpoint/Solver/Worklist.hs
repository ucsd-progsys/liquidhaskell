{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE TupleSections         #-}

module Language.Fixpoint.Solver.Worklist
       ( -- * Worklist type is opaque
         Worklist, Stats

         -- * Initialize
       , init

         -- * Pop off a constraint
       , pop

         -- * Add a constraint and all its dependencies
       , push

         -- * Constraints with Concrete RHS
       , unsatCandidates

         -- * Statistics
       , wRanks
       )
       where

import           Prelude hiding (init)
import           Language.Fixpoint.Types.PrettyPrint
import qualified Language.Fixpoint.Types   as F
import           Language.Fixpoint.Graph.Types
import           Language.Fixpoint.Graph   (isTarget)

import           Control.Arrow             (first)
import qualified Data.HashMap.Strict       as M
import qualified Data.Set                  as S
import qualified Data.List                 as L
import           Text.PrettyPrint.HughesPJ (text)

-- | Worklist ------------------------------------------------------------------

data Worklist a = WL { wCs     :: !WorkSet
                     , wPend   :: !(CMap ())
                     , wDeps   :: !(CMap [F.SubcId])
                     , wCm     :: !(CMap (F.SimpC a))
                     , wRankm  :: !(CMap Rank)
                     , wLast   :: !(Maybe F.SubcId)
                     , wRanks  :: !Int
                     , wTime   :: !Int
                     , wConcCs :: ![F.SubcId]
                     }

data Stats = Stats { numKvarCs  :: !Int
                   , numConcCs  :: !Int
                   , _numSccs   :: !Int
                   } deriving (Eq, Show)

instance PPrint (Worklist a) where
  pprintTidy k = pprintTidy k . S.toList . wCs

instance PTable Stats where
  ptable s = DocTable [ (text "# Sliced Constraints", pprint (numKvarCs s))
                      , (text "# Target Constraints", pprint (numConcCs s))
                      ]

instance PTable (Worklist a) where
  ptable = ptable . stats


-- | WorkItems ------------------------------------------------------------

type WorkSet  = S.Set WorkItem

data WorkItem = WorkItem { wiCId  :: !F.SubcId   -- ^ Constraint Id
                         , wiTime :: !Int   -- ^ Time at which inserted
                         , wiRank :: !Rank  -- ^ Rank of constraint
                         } deriving (Eq, Show)

instance PPrint WorkItem where
  pprintTidy _ = text . show

instance Ord WorkItem where
  compare (WorkItem i1 t1 r1) (WorkItem i2 t2 r2)
    = mconcat [ compare (rScc r1) (rScc r2)   -- SCC
              , compare t1 t2                 -- TimeStamp
              , compare (rIcc r1) (rIcc r2)   -- Inner SCC
              , compare (rTag r1) (rTag r2)   -- Tag
              , compare i1         i2         -- Otherwise Set drops items
              ]

--------------------------------------------------------------------------------
-- | Initialize worklist and slice out irrelevant constraints ------------------
--------------------------------------------------------------------------------
init :: SolverInfo a b -> Worklist a
--------------------------------------------------------------------------------
init sI    = WL { wCs     = items
                , wPend   = addPends M.empty kvarCs
                , wDeps   = cSucc cd
                , wCm     = cm
                , wRankm  = {- F.tracepp "W.init ranks" -} rankm
                , wLast   = Nothing
                , wRanks  = cNumScc cd
                , wTime   = 0
                , wConcCs = concCs
                }
  where
    cm        = F.cm  (siQuery sI)
    cd        = siDeps sI
    rankm     = cRank cd
    items     = S.fromList $ workItemsAt rankm 0 <$> kvarCs
    concCs    = fst <$> ics
    kvarCs    = fst <$> iks
    (ics,iks) = L.partition (isTarget . snd) (M.toList cm)

---------------------------------------------------------------------------
-- | Candidate Constraints to be checked AFTER computing Fixpoint ---------
---------------------------------------------------------------------------
unsatCandidates   :: Worklist a -> [F.SimpC a]
---------------------------------------------------------------------------
unsatCandidates w = [ lookupCMap (wCm w) i | i <- wConcCs w ]


---------------------------------------------------------------------------
pop  :: Worklist a -> Maybe (F.SimpC a, Worklist a, Bool, Int)
---------------------------------------------------------------------------
pop w = do
  (i, is) <- sPop $ wCs w
  Just ( lookupCMap (wCm w) i
       , popW w i is
       , newSCC w i
       , rank w i
       )

popW :: Worklist a -> F.SubcId -> WorkSet -> Worklist a
popW w i is = w { wCs   = is
                , wLast = Just i
                , wPend = remPend (wPend w) i }


newSCC :: Worklist a -> F.SubcId -> Bool
newSCC oldW i = (rScc <$> oldRank) /= (rScc <$> newRank)
  where
    oldRank   = lookupCMap rankm <$> wLast oldW
    newRank   = Just              $  lookupCMap rankm i
    rankm     = wRankm oldW

rank :: Worklist a -> F.SubcId -> Int
rank w i = rScc $ lookupCMap (wRankm w) i

---------------------------------------------------------------------------
push :: F.SimpC a -> Worklist a -> Worklist a
---------------------------------------------------------------------------
push c w = w { wCs   = sAdds (wCs w) wis'
             , wTime = 1 + t
             , wPend = addPends wp is'
             }
  where
    i    = F.subcId c
    is'  = filter (not . isPend wp) $ M.lookupDefault [] i (wDeps w)
    wis' = workItemsAt (wRankm w) t <$> is'
    t    = wTime w
    wp   = wPend w

workItemsAt :: CMap Rank -> Int -> F.SubcId -> WorkItem
workItemsAt !r !t !i = WorkItem { wiCId  = i
                                , wiTime = t
                                , wiRank = lookupCMap r i }



---------------------------------------------------------------------------
stats :: Worklist a -> Stats
---------------------------------------------------------------------------
stats w = Stats (kn w) (cn w) (wRanks w)
  where
    kn  = M.size . wCm
    cn  = length . wConcCs

---------------------------------------------------------------------------
-- | Pending API
---------------------------------------------------------------------------

addPends :: CMap () -> [F.SubcId] -> CMap ()
addPends = L.foldl' addPend

addPend :: CMap () -> F.SubcId -> CMap ()
addPend m i = M.insert i () m

remPend :: CMap () -> F.SubcId -> CMap ()
remPend m i = M.delete i m

isPend :: CMap () -> F.SubcId -> Bool
isPend w i = M.member i w

---------------------------------------------------------------------------
-- | Set API --------------------------------------------------------------
---------------------------------------------------------------------------

sAdds :: WorkSet -> [WorkItem] -> WorkSet
sAdds = L.foldl' (flip S.insert)

sPop :: WorkSet -> Maybe (F.SubcId, WorkSet)
sPop = fmap (first wiCId) . S.minView
