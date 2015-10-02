{-# LANGUAGE DeriveGeneric #-}

module Language.Fixpoint.Solver.Uniqify (renameAll) where

import           Language.Fixpoint.Types
import           Language.Fixpoint.Visitor (mapKVars')
import           Language.Fixpoint.Names (renameSymbol)
import           Language.Fixpoint.Solver.Eliminate (findWfC)
import           Language.Fixpoint.Misc  (fst3)
import qualified Data.HashMap.Strict     as M
import qualified Data.HashSet            as S
import           Data.List               ((\\), sort, foldl')
import           Data.Maybe              (catMaybes)
import           Data.Hashable
import           GHC.Generics            (Generic)
import           Control.Arrow           (second)
import           Control.DeepSeq

-- import           Control.Monad.State     (evalState, State, state)
-- import           Data.Foldable           (foldlM)

--------------------------------------------------------------
renameAll    :: SInfo a -> SInfo a
renameAll fi = fi'
  where
    fi'      = {-# SCC "renameVars" #-} renameVars fi $!! eids
    ids      = {-# SCC "ids"        #-} map fst3 $!! bindEnvToList $!! bs fi
    eids     = {-# SCC "toListExt"  #-} toListExtended ids $!! idm'
    idm'     = {-# SCC "invertMap"  #-} invertMap $!! idm
    idm      = {-# SCC "mkIdMap"    #-} mkIdMap fi
--------------------------------------------------------------

data Ref = RB BindId | RI Integer deriving (Eq, Generic)


instance NFData   Ref
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


type RnInfo a = (M.HashMap Symbol Sort, SInfo a)

renameVars :: SInfo a -> [(BindId, S.HashSet Ref)] -> SInfo a
renameVars fi xs = fi'
  where
    (_, fi')     = foldl' renameVarIfSeen (M.empty, fi) xs

renameVarIfSeen :: RnInfo a -> (BindId, S.HashSet Ref) -> RnInfo a
renameVarIfSeen (m, fi) x@(i, _)
  | M.member sym m = handleSeenVar fi x sym t m
  | otherwise      = (M.insert sym t m, fi)
  where
    (sym, t)       = second sr_sort $ lookupBindEnv i (bs fi)

handleSeenVar :: SInfo a -> (BindId, S.HashSet Ref) -> Symbol -> Sort -> M.HashMap Symbol Sort -> RnInfo a
handleSeenVar fi x sym t m
  | same      = (m, fi)
  | otherwise = (m, renameVar fi x) --TODO: do we need to send future collisions to the same new name?
  where
    same      = M.lookup sym m == Just t

-- | THIS IS TERRIBLE! Quadratic in the size of the environment!
renameVar :: SInfo a -> (BindId, S.HashSet Ref) -> SInfo a
renameVar fi (i, refs) = mapKVars' (updateKVars fi i sym sym') fi'' --TODO: optimize? (mapKVars separately on every rename is expensive)
  where
    sym  = fst $ lookupBindEnv i (bs fi)
    sym' = renameSymbol sym i
    sub  = (sym, eVar sym')
    fi'  = fi { bs = adjustBindEnv (`subst1` sub) i (bs fi) }
    fi'' = S.foldl' (applySub sub) fi' refs

applySub :: (Symbol, Expr) -> SInfo a -> Ref -> SInfo a
applySub sub fi (RB id) = fi { bs = adjustBindEnv go id (bs fi) }
  where
    go (sym, sr)        = (sym, subst1 sr sub)

applySub sub fi (RI id) = fi { cm = M.adjust go id (cm fi) }
  where
    go c                = c { crhs = subst1 (crhs c) sub }

updateKVars :: SInfo a -> BindId -> Symbol -> Symbol -> (KVar, Subst) -> Maybe Pred
updateKVars fi id oldSym newSym (k, Su su) =
  if relevant then Just $ PKVar k $ mkSubst [(newSym, eVar oldSym)] else Nothing
  where
    wfc = fst $ findWfC k (ws fi)
    relevant = (id `elem` elemsIBindEnv (wenv wfc)) && (oldSym `elem` map fst su)




-- renameVars fi xs = evalState (foldlM renameVarIfSeen fi xs) M.empty
-- renameVarIfSeen :: SInfo a -> (BindId, S.HashSet Ref) -> State (M.HashMap Symbol Sort) (SInfo a)
-- renameVarIfSeen fi x@(id, _) = state $ \m ->
  -- let (sym, t) = second sr_sort $ lookupBindEnv id (bs fi) in
  -- if sym `M.member` m
    -- then handleSeenVar fi x sym t m
    -- else (fi, M.insert sym srt m)
