{-# LANGUAGE PartialTypeSignatures #-}

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
import           Language.Fixpoint.Visitor (envKVars, kvars)
import           Language.Fixpoint.PrettyPrint (PPrint (..))
import           Language.Fixpoint.Misc (safeLookup, errorstar, fst3, sortNub, group)
import qualified Language.Fixpoint.Types   as F
import qualified Data.HashMap.Strict       as M
import qualified Data.Set                  as S
import qualified Data.List                 as L
import           Data.Maybe (fromMaybe)

import           Data.Graph (graphFromEdges, scc, path, Graph, Vertex)
import           Data.Tree (flatten)

---------------------------------------------------------------------------
-- | Worklist -------------------------------------------------------------
---------------------------------------------------------------------------

---------------------------------------------------------------------------
init :: F.SInfo a -> Worklist a
---------------------------------------------------------------------------
init fi    = WL { wCs    = S.fromList $ cRoots cd
                , wDeps  = cSucc cd
                , wCm    = F.cm fi
                , wRankm = cRank cd
                , wLast  = Nothing
                , wRanks = cNumScc cd }
  where
    cd     = cDeps fi

---------------------------------------------------------------------------
pop  :: Worklist a -> Maybe (F.SimpC a, Worklist a, Bool)
---------------------------------------------------------------------------
pop w = do
  (i, is) <- sPop $ wCs w
  Just ( getC (wCm w) i
       , w {wCs = is, wLast = Just i}
       , newSCC w i
       )

getC :: M.HashMap CId a -> CId -> a
getC cm i = fromMaybe err $ M.lookup i cm
  where
    err  = errorstar "getC: bad CId i"

newSCC :: Worklist a -> CId -> Bool
newSCC oldW i = oldRank /= newRank
  where
    oldRank   = getRank oldW <$> wLast oldW
    newRank   = Just          $  getRank oldW i

getRank :: Worklist a -> CId -> Rank
getRank w i = safeLookup err i (wRankm w)
  where
    err     = "getRank: cannot find SCC for " ++ show i

---------------------------------------------------------------------------
push :: F.SimpC a -> Worklist a -> Worklist a
---------------------------------------------------------------------------
push c w = w {wCs = sAdds (wCs w) js}
  where
    i    = sid' c
    js   = {- tracepp ("PUSH: id = " ++ show i) $ -} wDeps w i

sid'    :: F.SimpC a -> Integer
sid' c  = fromMaybe err $ F.sid c
  where
    err = errorstar "sid': SimpC without id"

---------------------------------------------------------------------------
ranks :: Worklist a -> Int
---------------------------------------------------------------------------
ranks = wRanks

---------------------------------------------------------------------------
-- | Worklist -------------------------------------------------------------
---------------------------------------------------------------------------

type Rank   = Int
type CId    = Integer
type CSucc  = CId -> [CId]
type CRank  = M.HashMap CId    Rank
type KVRead = M.HashMap F.KVar [CId]

data Worklist a = WL { wCs    :: S.Set CId
                     , wDeps  :: CSucc
                     , wCm    :: M.HashMap CId (F.SimpC a)
                     , wRankm :: CRank
                     , wLast  :: Maybe CId
                     , wRanks :: Int
                     }


instance PPrint (Worklist a) where
  pprint = pprint . S.toList . wCs

---------------------------------------------------------------------------
-- | Constraint Dependencies ----------------------------------------------
---------------------------------------------------------------------------

data CDeps = CDs { cRoots  :: ![CId]
                 , cSucc   :: CId -> [CId]
                 , cRank   :: CRank
                 , cNumScc :: Int
                 }

cDeps       :: F.SInfo a -> CDeps
cDeps fi    = CDs (map (fst3 . v) rs) next rankm nSccs
  where
    next    = kvSucc fi
    is      = M.keys $ F.cm fi
    es      = [(i, i, next i) | i <- is]
    (g,v,_) = graphFromEdges es
    rs      = filterRoots g sccs
    sccs    = L.reverse $ map flatten $ scc g
    rankm   = makeRank v sccs
    nSccs   = length sccs

makeRank :: (Vertex -> (CId, a, b)) -> [[Vertex]] -> CRank
makeRank g sccs = M.fromList irs
  where
    rvss        = zip [0..] sccs
    irs         = [(v2i v, r) | (r, vs) <- rvss, v <- vs ]
    v2i         = fst3 . g

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

succs :: M.HashMap CId (F.SimpC a) -> KVRead -> CSucc
succs cm rdBy i = sortNub $ concatMap kvReads iKs
  where
    ci          = getC cm i
    iKs         = kvars $ F.crhs ci
    kvReads k   = M.lookupDefault [] k rdBy

kvReadBy :: F.SInfo a -> KVRead
kvReadBy fi = group [ (k, i) | (i, ci) <- M.toList cm
                             , k       <- envKVars bs ci]
  where
    cm      = F.cm fi
    bs      = F.bs fi

---------------------------------------------------------------------------
-- | Set API --------------------------------------------------------------
---------------------------------------------------------------------------

sAdds :: (Ord a) => S.Set a -> [a] -> S.Set a
sAdds = L.foldl' (flip S.insert)

sPop :: S.Set a -> Maybe (a, S.Set a)
sPop = S.minView
