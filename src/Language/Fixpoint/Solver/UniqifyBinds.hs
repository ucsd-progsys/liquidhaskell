{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PatternGuards #-}

-- This module makes it so no binds with different sorts have the same name.

module Language.Fixpoint.Solver.UniqifyBinds (renameAll) where

import           Language.Fixpoint.Types
import           Language.Fixpoint.Solver.Types  (CId)
import           Language.Fixpoint.Misc          (fst3, mlookup)

import qualified Data.HashMap.Strict as M
import qualified Data.HashSet        as S
import qualified Data.List           as L
import           Data.Foldable       (foldl')
import           Data.Maybe          (catMaybes, fromJust, isJust)
import           Data.Hashable       (Hashable)
import           GHC.Generics        (Generic)
import           Control.Arrow       (second)
import           Control.DeepSeq     (NFData, ($!!))

--------------------------------------------------------------
renameAll    :: SInfo a -> SInfo a
renameAll fi2 = fi4
  where
    fi4      = {-# SCC "renameBinds" #-} renameBinds fi3 $!! rnm
    fi3      = {-# SCC "renameVars"  #-} renameVars fi2 rnm $!! idm
    rnm      = {-# SCC "mkRenameMap" #-} mkRenameMap $!! bs fi2
    idm      = {-# SCC "mkIdMap"     #-} mkIdMap fi2
--------------------------------------------------------------

data Ref = RB BindId | RI CId deriving (Eq, Generic)

instance NFData   Ref
instance Hashable Ref

-- stores for each constraint and BindId the set of other BindIds that it
-- references, i.e. those where it needs to know when their names gets changed
type IdMap = M.HashMap Ref (S.HashSet BindId)

-- map from old name and sort to new name, represented by a hashmap containing
-- association lists. Nothing as new name means same as old
type RenameMap = M.HashMap Symbol [(Sort, Maybe Symbol)]

--------------------------------------------------------------
mkIdMap :: SInfo a -> IdMap
--------------------------------------------------------------
mkIdMap fi = M.foldlWithKey' (updateIdMap $ bs fi) M.empty $ cm fi

updateIdMap :: BindEnv -> IdMap -> CId -> SimpC a -> IdMap
updateIdMap be m scId s = M.insertWith S.union (RI scId) refSet m'
  where
    ids = elemsIBindEnv $ senv s
    nameMap = M.fromList [(fst $ lookupBindEnv i be, i) | i <- ids]
    m' = foldl' (insertIdIdLinks be nameMap) m ids

    symSet = S.fromList $ syms $ crhs s
    refSet = namesToIds symSet nameMap

insertIdIdLinks :: BindEnv -> M.HashMap Symbol BindId -> IdMap -> BindId -> IdMap
insertIdIdLinks be nameMap m i = M.insertWith S.union (RB i) refSet m
  where
    sr = snd $ lookupBindEnv i be
    symSet = freeVars $ sr_reft sr
    refSet = namesToIds symSet nameMap

namesToIds :: S.HashSet Symbol -> M.HashMap Symbol BindId -> S.HashSet BindId
namesToIds syms m = S.fromList $ catMaybes [M.lookup sym m | sym <- S.toList syms] --TODO why any Nothings?

freeVars :: Reft -> S.HashSet Symbol
freeVars rft@(Reft (v, _)) = S.delete v $ S.fromList $ syms rft
--------------------------------------------------------------

--------------------------------------------------------------
mkRenameMap :: BindEnv -> RenameMap
--------------------------------------------------------------
mkRenameMap be = foldl' (addId be) M.empty ids
  where
    ids = fst3 <$> bindEnvToList be

addId :: BindEnv -> RenameMap -> BindId -> RenameMap
addId be m i
  | M.member sym m = addDupId m sym t i
  | otherwise      = M.insert sym [(t, Nothing)] m
  where
    (sym, t)       = second sr_sort $ lookupBindEnv i be

addDupId :: RenameMap -> Symbol -> Sort -> BindId -> RenameMap
addDupId m sym t i
  | isJust $ L.lookup t mapping = m
  | otherwise                   = M.insert sym ((t, Just $ renameSymbol sym i) : mapping) m
  where
    mapping = fromJust $ M.lookup sym m
--------------------------------------------------------------

--------------------------------------------------------------
renameVars :: SInfo a -> RenameMap -> IdMap -> SInfo a
--------------------------------------------------------------
renameVars fi rnMap idMap = M.foldlWithKey' (updateRef rnMap) fi idMap

updateRef :: RenameMap -> SInfo a -> Ref -> S.HashSet BindId -> SInfo a
updateRef rnMap fi rf bset = applySub (mkSubst subs) fi rf
  where
    symTList = [second sr_sort $ lookupBindEnv i $ bs fi | i <- S.toList bset]
    subs = catMaybes $ mkSubUsing rnMap <$> symTList

mkSubUsing :: RenameMap -> (Symbol, Sort) -> Maybe (Symbol, Expr)
mkSubUsing m (sym, t) = do
  newName <- fromJust $ L.lookup t $ mlookup m sym
  return (sym, eVar newName)

applySub :: Subst -> SInfo a -> Ref -> SInfo a
applySub sub fi (RB i) = fi { bs = adjustBindEnv go i (bs fi) }
  where
    go (sym, sr)        = (sym, subst sub sr)

applySub sub fi (RI i) = fi { cm = M.adjust go i (cm fi) }
  where
    go c                = c { _crhs = subst sub (_crhs c) }
--------------------------------------------------------------

--------------------------------------------------------------
renameBinds :: SInfo a -> RenameMap -> SInfo a
--------------------------------------------------------------
renameBinds fi m = fi { bs = bindEnvFromList $ renameBind m <$> beList }
  where
    beList = bindEnvToList $ bs fi

renameBind :: RenameMap -> (BindId, Symbol, SortedReft) -> (BindId, Symbol, SortedReft)
renameBind m (i, sym, sr)
  | (Just newSym) <- mnewSym = (i, newSym, sr)
  | otherwise                = (i, sym,    sr)
  where
    t       = sr_sort sr
    mnewSym = fromJust $ L.lookup t $ mlookup m sym
--------------------------------------------------------------
