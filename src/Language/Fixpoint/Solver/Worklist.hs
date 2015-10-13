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
import           Control.Arrow             (first)
import qualified Data.HashMap.Strict       as M
import qualified Data.Set                  as S
import qualified Data.List                 as L
import           Data.Maybe (fromMaybe)

import           Data.Graph (graphFromEdges, scc, path, Graph, Vertex)
import           Data.Tree (flatten)
import           Text.PrettyPrint.HughesPJ (text)
---------------------------------------------------------------------------
-- | Worklist -------------------------------------------------------------
---------------------------------------------------------------------------

---------------------------------------------------------------------------
init :: F.SInfo a -> Worklist a
---------------------------------------------------------------------------
init fi    = WL { wCs    = items
                , wDeps  = cSucc cd
                , wCm    = F.cm fi
                , wRankm = cRank cd
                , wLast  = Nothing
                , wRanks = cNumScc cd
                , wTime  = 0
                }
  where
    cd     = cDeps fi
    items  = S.fromList $ workItemsAt 0 <$> cRoots cd

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
push c w = w { wCs   = sAdds (wCs w) js
             , wTime = 1 + t       }
  where
    i    = sid' c
    js   = workItemsAt t <$> wDeps w i
    t    = wTime w

workItemsAt :: Int -> CId -> WorkItem
workItemsAt = error "FIXME"

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

type CId     = Integer
type CSucc   = CId -> [CId]
type CRank   = M.HashMap CId    Rank
type KVRead  = M.HashMap F.KVar [CId]
type WorkSet = S.Set WorkItem

data Worklist a = WL { wCs    :: WorkSet
                     , wDeps  :: CSucc
                     , wCm    :: M.HashMap CId (F.SimpC a)
                     , wRankm :: !CRank
                     , wLast  :: Maybe CId
                     , wRanks :: !Int
                     , wTime  :: !Int
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
makeRank g sccs = error "FIXME: makeRank" -- M.fromList irs
  -- where
    -- rvss        = zip [0..] sccs
    -- irs         = [(v2i v, r) | (r, vs) <- rvss, v <- vs ]
    -- v2i         = fst3 . g

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
-- | WorkItems ------------------------------------------------------------
---------------------------------------------------------------------------

data WorkItem = WorkItem { wiCId  :: !CId   -- ^ Constraint Id
                         , wiTime :: !Int   -- ^ Time at which inserted
                         , wiRank :: !Rank  -- ^ Rank of constraint
                         } deriving (Eq, Show)

instance PPrint WorkItem where
  pprint = text . show

instance Ord WorkItem where
  compare = cmpWI

cmpWI :: WorkItem -> WorkItem -> Ordering
cmpWI w1 w2 = mconcat [ cmp2 (rScc . wiRank) -- SCC
                      , cmp2 wiTime          -- TimeStamp
                      , cmp2 (rIcc . wiRank) -- Inner SCC
                      , cmp2 (rTag . wiRank) -- Tag
                      ]
  where
    cmp2 f  = compare (f w1) (f w2)
    wScc    = rScc . wiRank
    wTs     = wiTime


{- original OCAML implementation

   let compare (ts,r) (ts',r') =
     if r.scc <> r'.scc then compare r.scc r'.scc else
      if ts <> ts' then - (compare ts ts') else
        if r.iscc <> r'.iscc then compare r.iscc r'.iscc else
          if r.tag <> r'.tag then compare r.tag r'.tag else
            compare r.simpl r'.simpl
-}


lexOrder :: [Ordering] -> Ordering
lexOrder = mconcat

negOrder :: Ordering -> Ordering
negOrder EQ = EQ
negOrder LT = GT
negOrder GT = LT

---------------------------------------------------------------------------
-- | Ranks ----------------------------------------------------------------
---------------------------------------------------------------------------

data Rank = Rank { rScc  :: !Int    -- ^ SCC number with ALL dependencies
                 , rIcc  :: !Int    -- ^ SCC number without CUT dependencies
                 , rCut  :: !Bool   -- ^ Is the constraint RHS a CUT-VAR
                 , rTag  :: !F.Tag  -- ^ The constraint's Tag
                 } deriving (Eq, Show)

---------------------------------------------------------------------------
-- | Set API --------------------------------------------------------------
---------------------------------------------------------------------------

sAdds :: WorkSet -> [WorkItem] -> WorkSet
sAdds = L.foldl' (flip S.insert)

sPop :: WorkSet -> Maybe (CId, WorkSet)
sPop = fmap (first wiCId) . S.minView
