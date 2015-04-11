module Language.Fixpoint.Solver.Worklist
       ( -- * Worklist type is opaque
         Worklist

         -- * Initialize
       , init

         -- * Pop off a constraint
       , pop

         -- * Add a constraint and all its dependencies
       , push

       )
       where

import           Prelude hiding (init)
import           Language.Fixpoint.Solver.Deps
import           Language.Fixpoint.Misc
import           Language.Fixpoint.Config
import qualified Language.Fixpoint.Types   as F
import qualified Data.HashMap.Strict       as M
import qualified Data.Set                  as S
import qualified Data.List                 as L
import           Data.Maybe (fromMaybe)

---------------------------------------------------------------------------
-- | Worklist -------------------------------------------------------------
---------------------------------------------------------------------------

---------------------------------------------------------------------------
init :: Config -> F.FInfo a -> Worklist a
---------------------------------------------------------------------------
init _ fi = WL roots (cSucc cd) (F.cm fi)
  where
    cd    = cDeps fi
    roots = S.fromList $ cRoots cd

---------------------------------------------------------------------------
pop  :: Worklist a -> Maybe (F.SubC a, Worklist a)
---------------------------------------------------------------------------
pop w = do
  (i, is) <- sPop $ wCs w
  Just (getC (wCm w) i, w {wCs = is})

getC :: M.HashMap CId a -> CId -> a
getC cm i = fromMaybe err $ M.lookup i cm
  where
    err  = errorstar "getC: bad CId i"

---------------------------------------------------------------------------
push :: F.SubC a -> Worklist a -> Worklist a
---------------------------------------------------------------------------
push c w = w {wCs = sAdds (wCs w) js}
  where
    i    = sid' c
    js   = wDeps w i

sid'    :: F.SubC a -> Integer
sid' c  = fromMaybe err $ F.sid c
  where
    err = errorstar "sid': SubC without id"

---------------------------------------------------------------------------
-- | Worklist -------------------------------------------------------------
---------------------------------------------------------------------------

type CId    = Integer
type CSucc  = CId -> [CId]
type KVRead = M.HashMap F.KVar [CId]

data Worklist a = WL { wCs   :: S.Set CId
                     , wDeps :: CSucc
                     , wCm   :: M.HashMap CId (F.SubC a)
                     }

---------------------------------------------------------------------------
-- | Constraint Dependencies ----------------------------------------------
---------------------------------------------------------------------------

data CDeps = CDs { cRoots :: ![CId]
                 , cSucc  :: CId -> [CId]
                 }

cDeps :: F.FInfo a -> CDeps
cDeps fi = CDs rs next
  where
    next = kvSucc fi
    is   = M.keys $ F.cm fi
    is'  = concatMap next is
    rs   = sortDiff is is'

kvSucc :: F.FInfo a -> CSucc
kvSucc fi = succs cm rdBy
  where
    rdBy  = kvReadBy fi
    cm    = F.cm     fi

succs :: M.HashMap CId (F.SubC a) -> KVRead -> CSucc
succs cm rdBy i = sortNub $ concatMap kvReads iKs
  where
    ci          = getC cm i
    iKs         = rhsKVars ci
    kvReads k   = M.lookupDefault [] k rdBy

kvReadBy :: F.FInfo a -> KVRead
kvReadBy fi = group [ (k, i) | (i, ci) <- M.toList cm
                             , k       <- lhsKVars bs ci]
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

