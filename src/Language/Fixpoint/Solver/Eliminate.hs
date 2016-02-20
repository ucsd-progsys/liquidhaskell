{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE BangPatterns         #-}

module Language.Fixpoint.Solver.Eliminate (eliminate) where

import qualified Data.HashSet        as S
import qualified Data.HashMap.Strict as M

import           Language.Fixpoint.Types
import           Language.Fixpoint.Types.Visitor   (kvars, isConcC)
import           Language.Fixpoint.Partition       (depCuts, depNonCuts, deps)
import           Language.Fixpoint.Misc            (safeLookup, group, fst3, errorstar)

--------------------------------------------------------------------------------
eliminate :: SInfo a -> (Solution, SInfo a)
--------------------------------------------------------------------------------
eliminate si  = ( sHyp, si' )
  where
    sHyp      = solFromList [] kHyps
    si'       = cutSInfo   kI cKs si
    kHyps     = nonCutHyps kI nKs si
    kI        = kIndex  si
    (cKs,nKs) = kutVars si

kutVars :: SInfo a -> (S.HashSet KVar, S.HashSet KVar)
kutVars si   = (depCuts ds, depNonCuts ds)
  where
    ds       = deps si

--------------------------------------------------------------------------------
-- | Map each `KVar` to the list of constraints on which it appears on RHS
--------------------------------------------------------------------------------
type KIndex = M.HashMap KVar [Integer]

--------------------------------------------------------------------------------
kIndex     :: SInfo a -> KIndex
--------------------------------------------------------------------------------
kIndex si  = group [(k, i) | (i, c) <- iCs, k <- rkvars c]
  where
    iCs    = M.toList (cm si)
    rkvars = kvars . crhs

cutSInfo :: KIndex -> S.HashSet KVar -> SInfo a -> SInfo a
cutSInfo kI cKs si = si { ws = ws', cm = cm' }
  where
    ws'   = M.filterWithKey (\k _ -> S.member k cKs) (ws si)
    cm'   = M.filterWithKey (\i c -> S.member i cs || isConcC c) (cm si)
    cs    = S.fromList      (concatMap kCs cKs)
    kCs k = M.lookupDefault [] k kI

nonCutHyps :: KIndex -> S.HashSet KVar -> SInfo a -> [(KVar, Hyp)]
nonCutHyps kI nKs si = [ (k, nonCutHyp kI si k) | k <- S.toList nKs ]

nonCutHyp  :: KIndex -> SInfo a -> KVar -> Hyp
nonCutHyp kI si k = nonCutCube kDom <$> cs
  where
    kDom          = getDomain si k
    cs            = getSubC   si <$> M.lookupDefault [] k kI

nonCutCube :: [Symbol] -> SimpC a -> Cube
nonCutCube kDom c = Cube (senv c) (rhsSubst kDom c)

rhsSubst :: [Symbol] -> SimpC a -> Subst
rhsSubst kDom        = rsu . crhs
  where
    rsu (PKVar _ su) = filterSubst (\x _ -> x `elem` kDom) su
    rsu _            = errorstar "Eliminate.rhsSubst called on bad input"

domain :: BindEnv -> WfC a -> [Symbol]
domain be wfc = fst3 (wrft wfc) : map fst (envCs be $ wenv wfc)

getDomain :: SInfo a -> KVar -> [Symbol]
getDomain si k = domain (bs si) (getWfC si k)

getWfC :: SInfo a -> KVar -> WfC a
getWfC si k = ws si M.! k

getSubC :: SInfo a -> Integer -> SimpC a
getSubC si i = safeLookup msg i (cm si)
  where
    msg = "getSubC: " ++ show i

--------------------------------------------------------------------------------
{-
eliminateAll :: SInfo a -> (Solution, SInfo a)
eliminateAll !si = foldl' eliminate (mempty, si) nonCuts
  where
    nonCuts      = depNonCuts $ deps si

eliminate :: (Solution, SInfo a) -> KVar -> (Solution, SInfo a)
eliminate (!s, !si) k = (solInsert k (mkJVar orPred) s, si')
  where
    si'    = si { cm = nokCs , ws = M.delete k $ ws si }
    kCs    = M.filter (   elem k . kvars . crhs) (cm si) -- with    k in RHS (SLOW!)
    nokCs  = M.filter (notElem k . kvars . crhs) (cm si) -- without k in RHS (SLOW!)
    kW     = (ws si) M.! k
    kDom   = domain (bs si) kW
    orPred = POr $!! extractPred kDom (bs si)  <$> M.elems kCs

extractPred :: [Symbol] -> BindEnv -> SimpC a -> Expr
extractPred kDom be sc = renameQuantified (subcId sc) kSol
  where
    kSol               = PExist xts $ PAnd (lhsPreds ++ suPreds)
    xts                = filter (nonFunction be . fst) yts
    yts                = second sr_sort <$> env
    env                = clhs be sc
    lhsPreds           = bindPred <$> env
    suPreds            = substPreds kDom $ crhs sc

-- x:{v:int|v=10} -> (x=10)
bindPred :: (Symbol, SortedReft) -> Expr
bindPred (x, sr) = p `subst1`(v, eVar x)
  where
    v            = reftBind r
    r            = sr_reft sr
    p            = reftPred r

-- k0[v:=e1][x:=e2] -> [v = e1, x = e2]
substPreds :: [Symbol] -> Expr -> [Expr]
substPreds dom (PKVar _ (Su subs)) = [PAtom Eq (eVar x) e | (x, e) <- M.toList subs , x `elem` dom]
substPreds _ _ = errorstar "Eliminate.substPreds called on bad input"

-- SLOW!
nonFunction :: BindEnv -> Symbol -> Bool
nonFunction be sym = sym `notElem` funcs
  where
    funcs = [x | (_, x, sr) <- bindEnvToList be
               , isFunctionSortedReft sr]

renameQuantified :: Integer -> Expr -> Expr
renameQuantified i (PExist bs p) = PExist bs' p'
  where
    su  = substFromQBinds i bs
    bs' = first (subst su) <$> bs
    p'  = subst su p
renameQuantified _ _ = errorstar "Eliminate.renameQuantified called on bad input"

substFromQBinds :: Integer -> [(Symbol, Sort)] -> Subst
substFromQBinds i bs = Su $ M.fromList [(s, EVar $ existSymbol s i) | s <- fst <$> bs]

-}
