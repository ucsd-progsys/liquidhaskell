{-# LANGUAGE DeriveGeneric #-}

module Language.Fixpoint.Solver.Uniqify (renameAll) where

import           Language.Fixpoint.Types
import           Language.Fixpoint.Visitor (mapKVars')
import           Language.Fixpoint.Names (renameSymbol)
import           Language.Fixpoint.Solver.Eliminate (findWfC)
import           Language.Fixpoint.Misc  (fst3)
import qualified Data.HashMap.Strict     as M
import qualified Data.HashSet            as S
import           Data.List               ((\\), sort)
import           Data.Maybe              (catMaybes)
import           Data.Foldable           (foldlM)
import           Data.Hashable
import           GHC.Generics            (Generic)
import           Control.Monad.State     (evalState, State, state)
import           Control.Arrow           (second)

--------------------------------------------------------------
renameAll    :: SInfo a -> SInfo a
renameAll fi = renameVars fi $ toListExtended ids $ invertMap $ mkIdMap fi
  where
    ids      = map fst3 $ bindEnvToList $ bs fi
--------------------------------------------------------------

data Ref = RB BindId | RI Integer deriving (Eq, Generic)
instance Hashable Ref

-- stores for each constraint and BindId the set of other BindIds that it
-- references, i.e. those where it needs to know when their names gets changed
type IdMap = M.HashMap Ref (S.HashSet BindId)
type NameMap = M.HashMap Symbol BindId

invertMap   :: (Hashable k, Hashable v, Eq k, Eq v)
            => M.HashMap k (S.HashSet v) -> M.HashMap v (S.HashSet k)
invertMap m = M.fromListWith S.union entries
  where
    entries = [(v, S.singleton k) | (k, vs) <- M.toList m, v <- S.toList vs]

toListExtended :: [BindId] -> M.HashMap BindId (S.HashSet Ref) -> [(BindId, S.HashSet Ref)]
toListExtended ids m = [(id, M.lookupDefault S.empty id m) | id <- ids]

mkIdMap :: SInfo a -> IdMap
mkIdMap fi = M.foldlWithKey' (updateIdMap $ bs fi) M.empty $ cm fi

updateIdMap :: BindEnv -> IdMap -> Integer -> SimpC a -> IdMap
updateIdMap be m scId s = M.insertWith S.union (RI scId) refSet m'
  where
    ids = sort $ elemsIBindEnv $ senv s
    nameMap = M.fromList [(fst $ lookupBindEnv id be, id) | id <- ids]
    m' = foldl (insertIdIdLinks be nameMap) m ids

    symList = syms $ crhs s
    refSet = S.fromList $ namesToIds symList nameMap

insertIdIdLinks :: BindEnv -> NameMap -> IdMap -> BindId -> IdMap
insertIdIdLinks be nameMap m id = M.insertWith S.union (RB id) refSet m
  where
    sr = snd $ lookupBindEnv id be
    symList = freeVars $ sr_reft sr
    refSet = S.fromList $ namesToIds symList nameMap

namesToIds :: [Symbol] -> NameMap -> [BindId]
namesToIds syms m = catMaybes [M.lookup sym m | sym <- syms] --TODO why any Nothings?

freeVars :: Reft -> [Symbol]
freeVars reft@(Reft (v, _)) = syms reft \\ [v]


renameVars :: SInfo a -> [(BindId, S.HashSet Ref)] -> SInfo a
renameVars fi xs = evalState (foldlM renameVarIfSeen fi xs) M.empty

renameVarIfSeen :: SInfo a -> (BindId, S.HashSet Ref) -> State (M.HashMap Symbol Sort) (SInfo a)
renameVarIfSeen fi x@(id, _) = state (\m ->
  let (sym, srt) = second sr_sort $ lookupBindEnv id (bs fi) in
  if sym `M.member` m then handleSeenVar fi x sym srt m else (fi, M.insert sym srt m))

handleSeenVar :: SInfo a -> (BindId, S.HashSet Ref) -> Symbol -> Sort -> (M.HashMap Symbol Sort) -> (SInfo a, (M.HashMap Symbol Sort))
handleSeenVar fi x sym srt m | M.lookup sym m == Just srt = (fi, m)
                             | otherwise                  = (renameVar fi x, m) --TODO: do we need to send future collisions to the same new name?

renameVar :: SInfo a -> (BindId, S.HashSet Ref) -> SInfo a
renameVar fi (id, refs) = mapKVars' (updateKVars fi id sym sym') fi'' --TODO: optimize? (mapKVars separately on every rename is expensive)
  where
    sym = fst $ lookupBindEnv id (bs fi)
    sym' = renameSymbol sym id
    sub = (sym, eVar sym')
    go subst x = subst1 x subst
    fi' = fi { bs = adjustBindEnv (go sub) id (bs fi) }
    fi'' = S.foldl' (applySub sub) fi' refs

applySub :: (Symbol, Expr) -> SInfo a -> Ref -> SInfo a
applySub sub fi (RB id) = fi { bs = adjustBindEnv go id (bs fi) }
  where go (sym, sr) = (sym, subst1 sr sub)
applySub sub fi (RI id) = fi { cm = M.adjust go id (cm fi) }
  where go c = c { crhs = subst1 (crhs c) sub }

updateKVars :: SInfo a -> BindId -> Symbol -> Symbol -> (KVar, Subst) -> Maybe Pred
updateKVars fi id oldSym newSym (k, Su su) =
  if relevant then Just $ PKVar k $ mkSubst [(newSym, eVar oldSym)] else Nothing
  where
    wfc = fst $ findWfC k (ws fi)
    relevant = (id `elem` (elemsIBindEnv $ wenv wfc)) && (oldSym `elem` (map fst su))
