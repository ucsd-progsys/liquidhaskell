{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PatternGuards #-}

module Language.Fixpoint.Solver.Uniqify (renameAll) where

import           Language.Fixpoint.Types
import           Language.Fixpoint.Names            (renameSymbol)
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
renameAll fi = fi''
  where
    fi''     = {-# SCC "renameBinds" #-} renameBinds fi' $!! rnm
    fi'      = {-# SCC "renameVars"  #-} renameVars fi rnm $!! idm
    rnm      = {-# SCC "mkRenameMap" #-} mkRenameMap $!! bs fi
    idm      = {-# SCC "mkIdMap"     #-} mkIdMap fi
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

    symList = syms $ crhs s
    refSet = S.fromList $ namesToIds symList nameMap

insertIdIdLinks :: BindEnv -> M.HashMap Symbol BindId -> IdMap -> BindId -> IdMap
insertIdIdLinks be nameMap m i = M.insertWith S.union (RB i) refSet m
  where
    sr = snd $ lookupBindEnv i be
    symList = freeVars $ sr_reft sr
    refSet = S.fromList $ namesToIds symList nameMap

namesToIds :: [Symbol] -> M.HashMap Symbol BindId -> [BindId]
namesToIds syms m = catMaybes [M.lookup sym m | sym <- syms] --TODO why any Nothings?

freeVars :: Reft -> [Symbol]
freeVars rft@(Reft (v, _)) = L.delete v $ syms rft
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
    go (sym, sr)        = (sym, dsubst sub sr)

applySub sub fi (RI i) = fi { cm = M.adjust go i (cm fi) }
  where
    go c                = c { crhs = dsubst sub (crhs c) }
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


-- This class mirrors Subable exactly except when applying a Subst to a KVar.
-- In that case, it applies the Subst to both left and right hand sides of the
-- old subst rather than (telescopically) concatenating them, e.g.
-- dsubst [x:=y] k[x:=z] = k[y:=z]
-- subst  [x:=y] k[x:=z] = k[x:=z][x:=y] = k[x:=z]
class DSubable a where
  dsubst  :: Subst -> a -> a

instance DSubable Pred where
  dsubst su (PAnd ps)       = PAnd $ map (dsubst su) ps
  dsubst su (POr  ps)       = POr  $ map (dsubst su) ps
  dsubst su (PNot p)        = PNot $ dsubst su p
  dsubst su (PImp p1 p2)    = PImp (dsubst su p1) (dsubst su p2)
  dsubst su (PIff p1 p2)    = PIff (dsubst su p1) (dsubst su p2)
  dsubst su (PBexp e)       = PBexp $ subst su e
  dsubst su (PAtom r e1 e2) = PAtom r (subst su e1) (subst su e2)
  dsubst su (PKVar k su')   = PKVar k $ dsubst su su'
  dsubst _  (PAll _ _)      = error "dsubst: FORALL"
  dsubst _  p               = p

instance DSubable Refa where
  dsubst su (Refa p)       = Refa $ dsubst su p

instance DSubable Reft where
  dsubst su (Reft (v, ras))  = Reft (v, dsubst (substExcept su [v]) ras)

instance DSubable SortedReft where
  dsubst su (RR so r) = RR so $ dsubst su r

instance DSubable Subst where
  dsubst su (Su m) = Su $ M.fromList $ subst su $ M.toList m
