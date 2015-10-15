{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE BangPatterns          #-}

module Language.Fixpoint.Solver.Worklist
       ( -- * Worklist type is opaque
         Worklist

         -- * Initialize
       , init

         -- * Pop off a constraint
       , pop

         -- * Add a constraint and all its dependencies
       , push

         -- * Total number of SCCs
       , ranks
       )
       where

import           Prelude hiding (init)
import           Language.Fixpoint.Solver.Validate (isKvarC)
import           Language.Fixpoint.Visitor (envKVars, kvars)
import           Language.Fixpoint.PrettyPrint (PPrint (..))
import           Language.Fixpoint.Misc (safeLookup, fst3, sortNub, group)
import qualified Language.Fixpoint.Types   as F
import           Control.Arrow             (first)
import qualified Data.HashMap.Strict       as M
import qualified Data.Set                  as S
import qualified Data.List                 as L
-- import           Data.Maybe (fromMaybe)

import           Data.Graph (graphFromEdges, scc, path, Graph, Vertex)
import           Data.Tree (flatten)
import           Text.PrettyPrint.HughesPJ (text)

---------------------------------------------------------------------------
-- | Dramatis Personae
---------------------------------------------------------------------------

type CId     = Integer
type CSucc   = CId -> [CId]
type CMap a  = M.HashMap CId a

type KVRead  = M.HashMap F.KVar [CId]
type WorkSet = S.Set WorkItem
type DepEdge = (CId, CId, [CId])

-- | Worklist -------------------------------------------------------------

data Worklist a = WL { wCs    :: WorkSet
                     , wPend  :: CMap ()
                     , wDeps  :: CSucc
                     , wCm    :: CMap (F.SimpC a)
                     , wRankm :: CMap Rank
                     , wLast  :: Maybe CId
                     , wRanks :: !Int
                     , wTime  :: !Int
                     }

instance PPrint (Worklist a) where
  pprint = pprint . S.toList . wCs

-- | WorkItems ------------------------------------------------------------

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

-- | Ranks ----------------------------------------------------------------

data Rank = Rank { rScc  :: !Int    -- ^ SCC number with ALL dependencies
                 , rIcc  :: !Int    -- ^ SCC number without CUT dependencies
                 , rTag  :: !F.Tag  -- ^ The constraint's Tag
                 } deriving (Eq, Show)

---------------------------------------------------------------------------
init :: F.SInfo a -> Worklist a
---------------------------------------------------------------------------
init fi    = WL { wCs    = items               -- Add all constraints to worklist
                , wPend  = addPends M.empty is
                , wDeps  = cSucc cd
                , wCm    = cm
                , wRankm = rankm
                , wLast  = Nothing
                , wRanks = cNumScc cd
                , wTime  = 0
                }
  where
    cm     = F.cm  fi
    cd     = cDeps fi
    rankm  = cRank cd
    items  = S.fromList $ workItemsAt rankm 0 <$> is
    is     = iterCandidates fi

iterCandidates :: F.SInfo a -> [CId]
iterCandidates fi = [ i | (i, c) <- M.toList $ F.cm fi, isKvarC c]

---------------------------------------------------------------------------
pop  :: Worklist a -> Maybe (F.SimpC a, Worklist a, Bool)
---------------------------------------------------------------------------
pop w = do
  (i, is) <- sPop $ wCs w
  Just ( lookupCMap (wCm w) i
       , popW w i is
       , newSCC w i
       )

popW :: Worklist a -> CId -> WorkSet -> Worklist a
popW w i is = w {wCs = is, wLast = Just i, wPend = remPend (wPend w) i}


newSCC :: Worklist a -> CId -> Bool
newSCC oldW i = oldRank /= newRank
  where
    oldRank   = lookupCMap rankm <$> wLast oldW
    newRank   = Just              $  lookupCMap rankm i
    rankm     = wRankm oldW

lookupCMap :: CMap a -> CId -> a
lookupCMap rm i = safeLookup err i rm
  where
    err      = "lookupCMap: cannot find info for " ++ show i

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


-- sid'    :: F.SimpC a -> Integer
-- sid' c  = fromMaybe err $ F.sid c
--  where
--    err = errorstar "sid': SimpC without id"

---------------------------------------------------------------------------
ranks :: Worklist a -> Int
---------------------------------------------------------------------------
ranks = wRanks

---------------------------------------------------------------------------
-- | Constraint Dependencies ----------------------------------------------
---------------------------------------------------------------------------

data CDeps = CDs { cSucc   :: CSucc
                 , cRank   :: CMap Rank
                 , cNumScc :: Int
                 }

---------------------------------------------------------------------------
cDeps       :: F.SInfo a -> CDeps
---------------------------------------------------------------------------
cDeps fi       = CDs { cSucc   = next
                     , cRank   = makeRanks cm outRs inRs
                     , cNumScc = length sccs }
  where
    -- roots         = fst3 . vf <$> filterRoots g sccs
    next          = kvSucc fi
    es            = [(i, i, next i) | i <- M.keys cm]
    (g, vf, _)    = graphFromEdges es
    (outRs, sccs) = graphRanks g vf
    inRs          = if ks == mempty then outRs
                                    else inRanks cm es (F.kuts fi) outRs
    cm            = F.cm   fi
    ks            = F.kuts fi

graphRanks :: Graph -> (Vertex -> DepEdge) -> (CMap Int, [[Vertex]])
graphRanks g vf = (M.fromList irs, sccs)
  where
    irs        = [(v2i v, r) | (r, vs) <- rvss, v <- vs ]
    rvss       = zip [0..] sccs
    sccs       = L.reverse $ map flatten $ scc g
    v2i        = fst3 . vf

inRanks :: CMap (F.SimpC a) -> [DepEdge] -> F.Kuts -> CMap Int -> CMap Int
inRanks cm es ks outR = fst $ graphRanks g' vf'
  where
    (g', vf', _)      = graphFromEdges es'
    es'               = [(i, i, filter (not . isCut i) js) | (i,_,js) <- es ]
    isCut i j         = S.member i cutCIds && isEqOutRank i j
    isEqOutRank i j   = lookupCMap outR i == lookupCMap outR j
    cutCIds           = S.fromList [i | i <- M.keys cm, isKutWrite i ]
    isKutWrite        = any (`F.ksMember` ks) . kvWriteBy cm

makeRanks :: CMap (F.SimpC a) -> CMap Int -> CMap Int -> CMap Rank
makeRanks cm outR inR = M.fromList [(i, i2r i) | i <- M.keys cm]
  where
    i2r i             = Rank (outScc i) (inScc i) (tag i)
    outScc            = lookupCMap outR
    inScc             = lookupCMap inR
    tag               = F._ctag . lookupCMap cm

filterRoots :: Graph -> [[Vertex]] -> [Vertex]
filterRoots _ []         = []
filterRoots g (sCC:sccs) = sCC ++ filterRoots g rest
  where
    rest = filter (not . path g (head sCC) . head) sccs

kvSucc :: F.SInfo a -> CSucc
kvSucc fi = succs cm rdBy
  where
    rdBy  = kvReadBy fi
    cm    = F.cm     fi

succs :: CMap (F.SimpC a) -> KVRead -> CSucc
succs cm rdBy i = sortNub $ concatMap kvReads iKs
  where
    iKs         = kvWriteBy cm i
    kvReads k   = M.lookupDefault [] k rdBy

kvWriteBy :: CMap (F.SimpC a) -> CId -> [F.KVar]
kvWriteBy cm = kvars . F.crhs . lookupCMap cm

kvReadBy :: F.SInfo a -> KVRead
kvReadBy fi = group [ (k, i) | (i, ci) <- M.toList cm
                             , k       <- envKVars bs ci]
  where
    cm      = F.cm fi
    bs      = F.bs fi



{- original OCAML implementation

   let compare (ts,r) (ts',r') =
     if r.scc <> r'.scc then compare r.scc r'.scc else
      if ts <> ts' then - (compare ts ts') else
        if r.iscc <> r'.iscc then compare r.iscc r'.iscc else
          if r.tag <> r'.tag then compare r.tag r'.tag else
            compare r.simpl r'.simpl


lexOrder :: [Ordering] -> Ordering
lexOrder = mconcat

negOrder :: Ordering -> Ordering
negOrder EQ = EQ
negOrder LT = GT
negOrder GT = LT

-}


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
