
module Language.Fixpoint.Solver.Uniqify (renameAll) where

import           Language.Fixpoint.Types
import           Language.Fixpoint.Names (renameSymbol)
import           Language.Fixpoint.Misc  (errorstar)
import           Language.Fixpoint.Solver.Eliminate (elimKVar, findWfC)
import qualified Data.HashMap.Strict     as M
import qualified Data.HashSet            as S
import           Data.List               ((\\), sort)
import           Data.Maybe              (catMaybes)
import           Data.Foldable           (foldlM)
import           Control.Monad.State     (get, put, evalState, State)


--------------------------------------------------------------
renameAll :: FInfo a -> FInfo a
renameAll fi = renameVars fi $ M.toList $ mkIdMap fi
--------------------------------------------------------------


-- stores for each BindId the sets of other BindIds and constraints that
-- reference it, i.e. the ones that need to know when its name gets changed
type IdMap = M.HashMap BindId (S.HashSet BindId, S.HashSet Integer)
type NameMap = M.HashMap Symbol BindId

mkIdMap :: FInfo a -> IdMap
mkIdMap fi = M.foldlWithKey' (updateIdMap $ bs fi) M.empty $ cm fi

updateIdMap :: BindEnv -> IdMap -> Integer -> SubC a -> IdMap
updateIdMap be m subcId s = foldl (bar' subcId) m' refList
  where
    ids = sort $ elemsIBindEnv $ senv s
    nameMap = M.fromList [(fst $ lookupBindEnv id be, id) | id <- ids]
    m' = foldl (insertIdIdLink be nameMap) m ids

    symList = (freeVars $ sr_reft $ slhs s) ++ (freeVars $ sr_reft $ srhs s)
    refList = baz nameMap symList

insertIdIdLink :: BindEnv -> NameMap -> IdMap -> BindId -> IdMap
insertIdIdLink be nameMap idMap id = foldl (bar id) idMap refList
  where
    (_, sr) = lookupBindEnv id be
    symList = freeVars $ sr_reft sr
    refList = baz nameMap symList

bar :: BindId -> IdMap -> BindId -> IdMap
bar idOfReft m referencedId = M.insert referencedId (S.insert idOfReft bs, is) m
  where (bs, is) = M.lookupDefault (S.empty, S.empty) referencedId m

bar' :: Integer -> IdMap -> BindId -> IdMap
bar' idOfSubc m referencedId = M.insert referencedId (bs, S.insert idOfSubc is) m
  where (bs, is) = M.lookupDefault (S.empty, S.empty) referencedId m

baz :: NameMap -> [Symbol] -> [BindId]
baz m syms = catMaybes [M.lookup sym m | sym <- syms] --TODO why any Nothings?

freeVars :: Reft -> [Symbol]
freeVars reft@(Reft (v, _)) = syms reft \\ [v]


renameVars :: FInfo a -> [(BindId, (S.HashSet BindId, S.HashSet Integer))] -> FInfo a
renameVars fi xs = evalState (foldlM potentiallyRenameVar fi xs) S.empty

potentiallyRenameVar :: FInfo a -> (BindId, (S.HashSet BindId, S.HashSet Integer)) -> State (S.HashSet Symbol) (FInfo a)
potentiallyRenameVar fi x@(id, _) =
  do s <- get
     let (sym, _) = lookupBindEnv id (bs fi)
     let seen = sym `S.member` s
     put (if seen then s else (S.insert sym s))
     return (if seen then (renameVar fi x) else fi)

renameVar :: FInfo a -> (BindId, (S.HashSet BindId, S.HashSet Integer)) -> FInfo a
renameVar fi (id, stuff) = elimKVar (blarg fi id sym sym') fi''' --TODO: optimize? (elimKVar separately on every rename is expensive)
  where
    (sym, _) = lookupBindEnv id (bs fi)
    sym' = renameSymbol sym id
    sub = (sym, eVar sym')
    go subst x = subst1 x subst
    fi' = fi { bs = adjustBindEnv (go sub) id (bs fi) }
    fi'' = S.foldl' (foo sub) fi' (fst stuff)
    fi''' = S.foldl' (foo' sub) fi'' (snd stuff)

foo :: (Symbol, Expr) -> FInfo a -> BindId -> FInfo a
foo sub fi id = fi { bs = adjustBindEnv (go sub) id (bs fi) }
  where go sub (sym, sr) = (sym, subst1 sr sub)

foo' :: (Symbol, Expr) -> FInfo a -> Integer -> FInfo a
foo' sub fi id = fi { cm = M.adjust (go sub) id (cm fi) }
  where go sub c = c { slhs = subst1 (slhs c) sub ,
                       srhs = subst1 (srhs c) sub }

blarg :: FInfo a -> BindId -> Symbol -> Symbol -> (KVar, Subst) -> Maybe Pred
blarg fi id oldSym newSym (k, Su su) = if relevant then Just $ PKVar k $ mkSubst [(newSym, eVar oldSym)] else Nothing
  where
    wfc = fst $ findWfC k (ws fi)
    relevant = (id `elem` (elemsIBindEnv $ wenv wfc)) && (oldSym `elem` (map fst su))
