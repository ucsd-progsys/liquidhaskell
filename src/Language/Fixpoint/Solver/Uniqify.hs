
module Language.Fixpoint.Solver.Uniqify (renameAll) where

import           Language.Fixpoint.Types
import           Language.Fixpoint.Names (renameSymbol)
import           Language.Fixpoint.Misc  (errorstar)
import           Language.Fixpoint.Solver.Eliminate (elimKVar, findWfC)
import qualified Data.HashMap.Strict     as M
import           Data.List               ((\\), sort)
import           Data.Maybe              (catMaybes)


--------------------------------------------------------------
renameAll :: FInfo a -> FInfo a
renameAll fi = fi'
  where
    idMap = mkIdMap fi
    fi' = renameVars fi idMap
--------------------------------------------------------------

type IdMap   = M.HashMap BindId ([BindId], [Integer])
type NameMap = M.HashMap Symbol BindId

mkIdMap :: FInfo a -> IdMap
mkIdMap fi = M.foldlWithKey' (updateIdMap benv) (emptyIdMap benv) (cm fi)
  where benv = bs fi

emptyIdMap :: BindEnv -> IdMap
emptyIdMap benv = foldl go M.empty (M.keys $ beBinds benv)
  where go m b = M.insert b ([],[]) m

updateIdMap :: BindEnv -> IdMap -> Integer -> SubC a -> IdMap
updateIdMap benv m subcId s = foldl (bar' subcId) m' refList
  where
    ids = sort $ elemsIBindEnv $ senv s
    nameMap = mkNameMap benv ids
    m' = foldl (bongo benv nameMap) m ids

    symList = (freeVars $ sr_reft $ slhs s) ++ (freeVars $ sr_reft $ srhs s)
    refList = baz nameMap symList

bongo :: BindEnv -> NameMap -> IdMap -> BindId -> IdMap
bongo benv nameMap idMap id = foldl (bar id) idMap refList
  where
    (_, sr) = lookupBindEnv id benv
    symList = freeVars $ sr_reft sr
    refList = baz nameMap symList

bar :: BindId -> IdMap -> BindId -> IdMap
bar idOfReft m referencedId = M.insert referencedId (idOfReft : bs, is) m
  where (bs, is) = M.lookupDefault (errorstar "wat") referencedId m

bar' :: Integer -> IdMap -> BindId -> IdMap
bar' idOfSubc m referencedId = M.insert referencedId (bs, idOfSubc : is) m
  where (bs, is) = M.lookupDefault (errorstar "wat") referencedId m

baz :: NameMap -> [Symbol] -> [BindId]
baz m syms = catMaybes [M.lookup sym m | sym <- syms] --TODO why any Nothings?

freeVars :: Reft -> [Symbol]
freeVars reft@(Reft (v, _)) = syms reft \\ [v]

mkNameMap :: BindEnv -> [BindId] -> NameMap
mkNameMap benv ids = foldl (insertInverse benv) M.empty ids

insertInverse :: BindEnv -> NameMap -> BindId -> NameMap
insertInverse benv m id = M.insert sym id m
  where (sym, _) = lookupBindEnv id benv

renameVars :: FInfo a -> IdMap -> FInfo a
renameVars = M.foldlWithKey' renameVar

renameVar :: FInfo a -> BindId -> ([BindId], [Integer]) -> FInfo a
renameVar fi id stuff = elimKVar (blarg fi id sym sym') fi''' --TODO: optimize? (elimKVar separately on every rename is expensive)
  where
    (sym, _) = lookupBindEnv id (bs fi)
    sym' = renameSymbol sym id
    sub = (sym, eVar sym')
    go subst x = subst1 x subst
    fi' = fi { bs = adjustBindEnv (go sub) id (bs fi) }
    fi'' = foldl (foo sub) fi' (fst stuff)
    fi''' = foldl (foo' sub) fi'' (snd stuff)

foo :: (Symbol, Expr) -> FInfo a -> BindId -> FInfo a
foo sub fi id = fi { bs = adjustBindEnv (go sub) id (bs fi) }
  where go sub (sym, sr) = (sym, subst1 sr sub)

foo' :: (Symbol, Expr) -> FInfo a -> Integer -> FInfo a
foo' sub fi id = fi { cm = M.adjust (go sub) id (cm fi) }
  where go sub c = c { slhs = subst1 (slhs c) sub ,
                       srhs = subst1 (srhs c) sub }

blarg :: FInfo a -> BindId -> Symbol -> Symbol -> KVar -> Maybe Pred
blarg fi id oldSym newSym k = if relevant then Just $ PKVar k $ mkSubst [(newSym, eVar oldSym)] else Nothing
  where
    wfc = fst $ findWfC k (ws fi)
    relevant = id `elem` (elemsIBindEnv $ wenv wfc)
