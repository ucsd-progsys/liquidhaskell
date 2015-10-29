{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PatternGuards #-}

module Language.Fixpoint.Solver.Uniqify (renameAll) where

import           Language.Fixpoint.Types
import           Language.Fixpoint.Visitor          (mapKVarSubsts)
import           Language.Fixpoint.Names            (renameSymbol, kArgSymbol)
import           Language.Fixpoint.Misc             (fst3, mlookup)
import qualified Data.HashMap.Strict                as M
import qualified Data.HashSet                       as S
import qualified Data.List                          as L
import           Data.Foldable                      (foldl')
import           Data.Maybe                         (catMaybes, fromJust, isJust)
import           Data.Hashable                      (Hashable)
import           GHC.Generics                       (Generic)
import           Control.Arrow                      (second)
import           Control.DeepSeq                    (NFData, ($!!))

--------------------------------------------------------------
renameAll    :: SInfo a -> SInfo a
renameAll fi0 = fi4
  where
    fi4      = {-# SCC "renameBinds" #-} renameBinds fi3 $!! rnm
    fi3      = {-# SCC "renameVars"  #-} renameVars fi2 rnm $!! idm
    rnm      = {-# SCC "mkRenameMap" #-} mkRenameMap $!! bs fi2
    idm      = {-# SCC "mkIdMap"     #-} mkIdMap fi2
    fi2      = {-# SCC "updateWfcs"  #-} updateWfcs fi1
    fi1      = {-# SCC "remakeSubsts" #-} remakeSubsts fi0
--------------------------------------------------------------

data Ref = RB BindId | RI Integer deriving (Eq, Generic)

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

updateIdMap :: BindEnv -> IdMap -> Integer -> SimpC a -> IdMap
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

--------------------------------------------------------------
remakeSubsts :: SInfo a -> SInfo a
--------------------------------------------------------------
remakeSubsts fi = mapKVarSubsts (remakeSubstIfWfcExists fi) fi

--TODO: why are there kvars with no WfC?
remakeSubstIfWfcExists :: SInfo a -> KVar -> Subst -> Subst
remakeSubstIfWfcExists fi k su
  | k `M.member` ws fi = remakeSubst fi k su
  | otherwise          = Su M.empty

remakeSubst :: SInfo a -> KVar -> Subst -> Subst
remakeSubst fi k su = foldl' (updateSubst k) su names
  where
    w = (ws fi) M.! k
    names = (fst3 $ wrft w) : (fst <$> envCs (bs fi) (wenv w))

updateSubst :: KVar -> Subst -> Symbol -> Subst
updateSubst k (Su su) sym 
  | sym `M.member` su = Su $ M.delete sym $ M.insert (kArgSymbol' sym k) (su M.! sym) su
  | otherwise = Su $ M.insert (kArgSymbol' sym k) (eVar sym) su
--------------------------------------------------------------

--------------------------------------------------------------
updateWfcs :: SInfo a -> SInfo a
--------------------------------------------------------------
updateWfcs fi = M.foldl' (updateWfc $ bs fi) fi (ws fi)

updateWfc :: BindEnv -> SInfo a -> WfC a -> SInfo a
updateWfc be fi w = fi' { ws = M.insert k w' (ws fi) }
  where
    (v, t, k) = wrft w
    (fi', newIds) = insertNewBinds w fi k
    env' = insertsIBindEnv newIds emptyIBindEnv
    w' = w { wenv = env', wrft = (kArgSymbol' v k, t, k) }

insertNewBinds :: WfC a -> SInfo a -> KVar -> (SInfo a, [BindId])
insertNewBinds w fi k = foldl' (accumBindsIfValid k) (fi, []) (elemsIBindEnv $ wenv w)

accumBindsIfValid :: KVar -> (SInfo a, [BindId]) -> BindId -> (SInfo a, [BindId])
accumBindsIfValid k (fi, ids) i = if renamable then accumBinds k (fi, ids) i else (fi, i : ids)
  where
    --TODO: is ignoring the old SortedReft ok? what would it mean if it were non-trivial in a wf environment?
    (oldSym, sr) = lookupBindEnv i (bs fi)
    renamable = isValidInRefinements $ sr_sort sr

accumBinds :: KVar -> (SInfo a, [BindId]) -> BindId -> (SInfo a, [BindId])
accumBinds k (fi, ids) i = (fi {bs = be'}, i' : ids)
  where
    --TODO: is ignoring the old SortedReft ok? what would it mean if it were non-trivial in a wf environment?
    (oldSym, sr) = lookupBindEnv i (bs fi)
    newSym = kArgSymbol' oldSym k
    (i', be') = insertBindEnv newSym sr (bs fi)
--------------------------------------------------------------

kArgSymbol' :: Symbol -> KVar -> Symbol
kArgSymbol' sym k = (kArgSymbol sym) `mappend` (symbol "_") `mappend` (kv k)

isValidInRefinements :: Sort -> Bool
isValidInRefinements FInt        = True
isValidInRefinements FReal       = True
isValidInRefinements FNum        = False
isValidInRefinements FFrac       = False
isValidInRefinements (FObj _)    = True
isValidInRefinements (FVar _)    = True
isValidInRefinements (FFunc _ _) = False
isValidInRefinements (FTC _)     = True --TODO is this true? seems to be required for e.g. ResolvePred.hs
isValidInRefinements (FApp _ _)  = True
