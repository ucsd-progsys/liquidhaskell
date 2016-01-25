{-# LANGUAGE PartialTypeSignatures #-}
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
import           Language.Fixpoint.Types.PrettyPrint -- (PTable (..), PPrint (..))
import qualified Language.Fixpoint.Types   as F
import           Language.Fixpoint.Solver.Types
import           Language.Fixpoint.Solver.Graph
import           Control.Arrow             (first)
import qualified Data.HashMap.Strict       as M
import qualified Data.Set                  as S
import qualified Data.List                 as L
import           Data.Graph (graphFromEdges)
import           Text.PrettyPrint.HughesPJ (text)

-- | Worklist -------------------------------------------------------------

data Worklist a = WL { wCs     :: !WorkSet
                     , wPend   :: !(CMap ())
                     , wDeps   :: CSucc
                     , wCm     :: !(CMap (F.SimpC a))
                     , wRankm  :: !(CMap Rank)
                     , wLast   :: !(Maybe CId)
                     , wRanks  :: !Int
                     , wTime   :: !Int
                     , wConcCs :: ![CId]
                     }

data Stats = Stats { numKvarCs  :: !Int
                   , numConcCs  :: !Int
                   , _numSccs   :: !Int
                   } deriving (Eq, Show)


instance PPrint (Worklist a) where
  pprint = pprint . S.toList . wCs

instance PTable Stats where
  ptable s = DocTable [ (text "# Sliced Constraints", pprint (numKvarCs s))
                      , (text "# Target Constraints", pprint (numConcCs s))
                      ]

instance PTable (Worklist a) where
  ptable = ptable . stats


-- | WorkItems ------------------------------------------------------------

type WorkSet  = S.Set WorkItem

data WorkItem = WorkItem { wiCId  :: !CId   -- ^ Constraint Id
                         , wiTime :: !Int   -- ^ Time at which inserted
                         , wiRank :: !Rank  -- ^ Rank of constraint
                         } deriving (Eq, Show)

instance PPrint WorkItem where
  pprint = text . show

instance Ord WorkItem where
  compare (WorkItem i1 t1 r1) (WorkItem i2 t2 r2)
    = mconcat [ compare (rScc r1) (rScc r2)   -- SCC
              , compare t1 t2                 -- TimeStamp
              , compare (rIcc r1) (rIcc r2)   -- Inner SCC
              , compare (rTag r1) (rTag r2)   -- Tag
              , compare i1         i2         -- Otherwise Set drops items
              ]

-- | Ranks ---------------------------------------------------------------------

data Rank = Rank { rScc  :: !Int    -- ^ SCC number with ALL dependencies
                 , rIcc  :: !Int    -- ^ SCC number without CUT dependencies
                 , rTag  :: !F.Tag  -- ^ The constraint's Tag
                 } deriving (Eq, Show)

--------------------------------------------------------------------------------
-- | Initialize worklist and slice out irrelevant constraints ------------------
--------------------------------------------------------------------------------
init :: F.SInfo a -> Worklist a
--------------------------------------------------------------------------------
init fi    = WL { wCs     = items
                , wPend   = addPends M.empty kvarCs
                , wDeps   = cSucc cd
                , wCm     = cm
                , wRankm  = rankm
                , wLast   = Nothing
                , wRanks  = cNumScc cd
                , wTime   = 0
                , wConcCs = concCs
                }
  where
    cm        = F.cm  fi
    cd        = cDeps fi
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

popW :: Worklist a -> CId -> WorkSet -> Worklist a
popW w i is = w { wCs   = is
                , wLast = Just i
                , wPend = remPend (wPend w) i }


newSCC :: Worklist a -> CId -> Bool
newSCC oldW i = (rScc <$> oldRank) /= (rScc <$> newRank)
  where
    oldRank   = lookupCMap rankm <$> wLast oldW
    newRank   = Just              $  lookupCMap rankm i
    rankm     = wRankm oldW

rank :: Worklist a -> CId -> Int
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
    is'  = filter (not . isPend wp) $ wDeps w i
    wis' = workItemsAt (wRankm w) t <$> is'
    t    = wTime w
    wp   = wPend w

workItemsAt :: CMap Rank -> Int -> CId -> WorkItem
workItemsAt !r !t !i = WorkItem { wiCId  = i
                                , wiTime = t
                                , wiRank = lookupCMap r i }

---------------------------------------------------------------------------
-- | Constraint Dependencies ----------------------------------------------
---------------------------------------------------------------------------

data CDeps = CDs { cSucc   :: CSucc
                 , cRank   :: CMap Rank
                 , cNumScc :: Int
                 }

---------------------------------------------------------------------------
cDeps :: F.SInfo a -> CDeps
---------------------------------------------------------------------------
cDeps fi  = CDs { cSucc   = gSucc cg
                , cNumScc = gSccs cg
                , cRank   = M.fromList [(i, rf i) | i <- is ]
                }
  where
    rf    = rankF (F.cm fi) outRs inRs
    inRs  = inRanks fi es outRs
    outRs = gRanks cg
    es    = gEdges cg
    cg    = cGraph fi
    cm    = F.cm fi
    is    = M.keys cm

rankF :: CMap (F.SimpC a) -> CMap Int -> CMap Int -> CId -> Rank
rankF cm outR inR = \i -> Rank (outScc i) (inScc i) (tag i)
  where
    outScc        = lookupCMap outR
    inScc         = lookupCMap inR
    tag           = F._ctag . lookupCMap cm



---------------------------------------------------------------------------
inRanks :: F.SInfo a -> [DepEdge] -> CMap Int -> CMap Int
---------------------------------------------------------------------------
inRanks fi es outR
  | ks == mempty      = outR
  | otherwise         = fst $ graphRanks g' vf'
  where
    ks                = F.kuts fi
    cm                = F.cm fi
    (g', vf', _)      = graphFromEdges es'
    es'               = [(i, i, filter (not . isCut i) js) | (i,_,js) <- es ]
    isCut i j         = S.member i cutCIds && isEqOutRank i j
    isEqOutRank i j   = lookupCMap outR i == lookupCMap outR j
    cutCIds           = S.fromList [i | i <- M.keys cm, isKutWrite i ]
    isKutWrite        = any (`F.ksMember` ks) . kvWriteBy cm


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

addPends :: CMap () -> [CId] -> CMap ()
addPends = L.foldl' addPend

addPend :: CMap () -> CId -> CMap ()
addPend m i = M.insert i () m

remPend :: CMap () -> CId -> CMap ()
remPend m i = M.delete i m

isPend :: CMap () -> CId -> Bool
isPend w i = M.member i w

---------------------------------------------------------------------------
-- | Set API --------------------------------------------------------------
---------------------------------------------------------------------------

sAdds :: WorkSet -> [WorkItem] -> WorkSet
sAdds = L.foldl' (flip S.insert)

sPop :: WorkSet -> Maybe (CId, WorkSet)
sPop = fmap (first wiCId) . S.minView
