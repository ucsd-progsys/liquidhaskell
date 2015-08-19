{-# LANGUAGE DeriveGeneric              #-}

module Language.Fixpoint.Solver.Uniqify (renameAll) where

import           Language.Fixpoint.Types
import           Language.Fixpoint.Names (renameSymbol)
import           Language.Fixpoint.Solver.Eliminate (elimKVar, findWfC)
import qualified Data.HashMap.Strict     as M
import qualified Data.HashSet            as S
import           Data.List               ((\\), sort)
import           Data.Maybe              (catMaybes)
import           Data.Foldable           (foldlM)
import           Control.Monad.State     (get, put, evalState, State)

import           Data.Hashable
import           GHC.Generics              (Generic)

--------------------------------------------------------------
renameAll :: FInfo a -> FInfo a
renameAll fi = renameVars fi $ M.toList $ invert $ mkIdMap fi
--------------------------------------------------------------

data Ref = RB BindId | RI Integer
  deriving (Eq, Generic)
instance Hashable Ref

-- stores for each constraint and each BindId the sets of other BindIds that
-- it references, i.e. the ones where it needs to know when their names gets changed
type IdMap = M.HashMap Ref (S.HashSet BindId)
type NameMap = M.HashMap Symbol BindId

invert :: IdMap -> M.HashMap BindId (S.HashSet Ref)
invert m = M.fromListWith S.union entries
  where 
    entries = [(v, S.singleton k) | (k, vs) <- M.toList m, v <- S.toList vs]


mkIdMap :: FInfo a -> IdMap
mkIdMap fi = M.foldlWithKey' (updateIdMap $ bs fi) M.empty $ cm fi

updateIdMap :: BindEnv -> IdMap -> Integer -> SubC a -> IdMap
updateIdMap be m subcId s = M.insertWith S.union (RI subcId) refSet m'
  where
    ids = sort $ elemsIBindEnv $ senv s
    nameMap = M.fromList [(fst $ lookupBindEnv id be, id) | id <- ids]
    m' = foldl (insertIdIdLinks be nameMap) m ids

    symList = (freeVars $ sr_reft $ slhs s) ++ (freeVars $ sr_reft $ srhs s)
    refSet = S.fromList $ namesToIds symList nameMap

insertIdIdLinks :: BindEnv -> NameMap -> IdMap -> BindId -> IdMap
insertIdIdLinks be nameMap m id = M.insertWith S.union (RB id) refSet m
  where
    (_, sr) = lookupBindEnv id be
    symList = freeVars $ sr_reft sr
    refSet = S.fromList $ namesToIds symList nameMap

namesToIds :: [Symbol] -> NameMap -> [BindId]
namesToIds syms m = catMaybes [M.lookup sym m | sym <- syms] --TODO why any Nothings?

freeVars :: Reft -> [Symbol]
freeVars reft@(Reft (v, _)) = syms reft \\ [v]


renameVars :: FInfo a -> [(BindId, S.HashSet Ref)] -> FInfo a
renameVars fi xs = evalState (foldlM renameVarIfSeen fi xs) S.empty

renameVarIfSeen :: FInfo a -> (BindId, S.HashSet Ref) -> State (S.HashSet Symbol) (FInfo a)
renameVarIfSeen fi x@(id, _) =
  do s <- get
     let sym = fst $ lookupBindEnv id (bs fi)
     let seen = sym `S.member` s
     put (if seen then s else (S.insert sym s))
     return (if seen then (renameVar fi x) else fi)

renameVar :: FInfo a -> (BindId, S.HashSet Ref) -> FInfo a
renameVar fi (id, stuff) = elimKVar (blarg fi id sym sym') fi'' --TODO: optimize? (elimKVar separately on every rename is expensive)
  where
    sym = fst $ lookupBindEnv id (bs fi)
    sym' = renameSymbol sym id
    sub = (sym, eVar sym')
    go subst x = subst1 x subst
    fi' = fi { bs = adjustBindEnv (go sub) id (bs fi) }
    fi'' = S.foldl' (foo sub) fi' stuff

foo :: (Symbol, Expr) -> FInfo a -> Ref -> FInfo a
foo sub fi (RB id) = fi { bs = adjustBindEnv (go sub) id (bs fi) }
  where go sub (sym, sr) = (sym, subst1 sr sub)
foo sub fi (RI id) = fi { cm = M.adjust (go sub) id (cm fi) }
  where go sub c = c { slhs = subst1 (slhs c) sub ,
                       srhs = subst1 (srhs c) sub }

blarg :: FInfo a -> BindId -> Symbol -> Symbol -> (KVar, Subst) -> Maybe Pred
blarg fi id oldSym newSym (k, Su su) = if relevant then Just $ PKVar k $ mkSubst [(newSym, eVar oldSym)] else Nothing
  where
    wfc = fst $ findWfC k (ws fi)
    relevant = (id `elem` (elemsIBindEnv $ wenv wfc)) && (oldSym `elem` (map fst su))
