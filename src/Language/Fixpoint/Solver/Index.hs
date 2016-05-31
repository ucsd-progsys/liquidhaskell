-- | This module contains the code for the new "fast" solver, that creates
--   bit-indexed propositions for each binder and constraint-id, links them
--   via the environment dominator tree, after which each lhsPred is simply
--   a conjunction of the RHS binder and the "current" solutions for dependent
--   (cut) KVars.

-- TODO: backgroundPred, lhsPred, hook into the ACTUAL SOLVER

{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE OverloadedStrings     #-}

module Language.Fixpoint.Solver.Index (

    -- * Constructor
      create

    -- * BackGround Predicate
    , bgPred

    -- * LHS Predicate
    , lhsPred

    , mkDoms
    ) where

import           Language.Fixpoint.Misc
import           Language.Fixpoint.Types.Config
import qualified Language.Fixpoint.Types            as F
import           Language.Fixpoint.Types                 ((&.&))
import           Language.Fixpoint.Types.Solutions
import           Language.Fixpoint.Graph            (CDeps (..))

import qualified Data.HashMap.Strict  as M
-- import qualified Data.HashSet         as S
import qualified Data.Graph.Inductive as G
import qualified Data.List            as L

--------------------------------------------------------------------------------
-- | Creating an Index ---------------------------------------------------------
--------------------------------------------------------------------------------
create :: Config -> F.SInfo a -> [(F.KVar, Hyp)] -> CDeps -> Index
--------------------------------------------------------------------------------
create _cfg sI kHyps _cDs = FastIdx
  { bindExpr = bE
  , kvUse    = kU
  , bindPrev = mkBindPrev sI
  , kvDef    = M.fromList kHyps
  , kvDeps   = error "TBD:kvDeps" -- cPrev cDs
  }
  where
    (bE, kU) = mkBindExpr sI


--------------------------------------------------------------------------------
mkBindExpr :: F.SInfo a -> (F.BindId |-> BindPred, KIndex |-> F.KVSub)
mkBindExpr sI = (M.fromList ips, M.fromList kSus)
  where
    kSus = [ (k, kSu)                | (_, _, iks) <- ipks, (k, kSu) <- iks    ]
    ips  = [ (i, BP p (fst <$> iks)) | (i, p, iks) <- ipks                     ]
    ipks = [ (i, p, iks)             | (i, x, r)   <- F.bindEnvToList (F.bs sI)
                                     , let (p, iks) = mkBindPred i x r         ]

mkBindPred :: F.BindId -> F.Symbol -> F.SortedReft -> (F.Pred, [(KIndex, F.KVSub)])
mkBindPred i x sr = (F.pAnd ps, zipWith tx [0..] ks)
  where
    (ps, ks)      = F.sortedReftConcKVars x sr
    tx j k@(kv,_) = (KIndex (Bind i) j kv, k)

--------------------------------------------------------------------------------
mkBindPrev :: F.SInfo a -> (BIndex |-> BIndex)
mkBindPrev sI = M.fromList [(intBIndex i, intBIndex j) | (i, j) <- iDoms]
  where
    iDoms     = mkDoms bindIds cEnvs
    bindIds   = fst3   <$> F.bindEnvToList (F.bs sI)
    cEnvs     = [(i, cBinds be) | (i, be) <- M.toList (F.cm sI) ]
    cBinds    = F.elemsIBindEnv . F.senv

-- >>> mkDoms [1,2,3,4,5] [[1,2,3], [1,2,4], [1,5]]
-- [(2,1),(3,2),(4,2),(5,1)]
mkDoms :: ListNE F.BindId -> [(F.SubcId, [F.BindId])] -> [(Int, Int)]
mkDoms is envs  = G.iDom (mkEnvTree is envs) (minimum is)

mkEnvTree :: [F.BindId] -> [(F.SubcId, [F.BindId])] -> G.Gr Int ()
mkEnvTree is envs
  | isTree es   = G.mkGraph vs es
  | otherwise   = error "mkBindPrev: Malformed environments -- not tree-like! (TODO: move into Validate)"
  where
    vs          = node <$> (Bind <$> is)  ++ (Cstr . fst <$> envs)
    es          = edge <$> concatMap envEdges envs
    node i      = (bIndexInt i, bIndexInt i)
    edge (i, j) = (bIndexInt i, bIndexInt j, ())

envEdges :: (F.SubcId, [F.BindId]) -> [(BIndex, BIndex)]
envEdges (i,js) = (maximum js', Cstr i) : buddies js'
  where
    js'         = intBIndex <$> L.sort js

bIndexInt :: BIndex -> Int
bIndexInt (Bind i) = i
bIndexInt (Cstr j) = fromIntegral (negate j)

intBIndex :: Int -> BIndex
intBIndex i
  | 0 <= i    = Bind i
  | otherwise = Cstr (fromIntegral i)


-- TODO: push the `isTree` check into Validate
isTree :: (EqHash k) => [(k, k, a)] -> Bool
isTree es    = allMap (sizeLE 1) inEs
  where
    inEs     = group [ (j, i) | (i, j, _) <- es]
    sizeLE n = (<= n) . length . sortNub

buddies :: [a] -> [(a, a)]
buddies (x:y:zs) = (x, y) : buddies (y:zs)
buddies _        = []

--------------------------------------------------------------------------------
-- | Encoding _all_ constraints as a single background predicate ---------------
--------------------------------------------------------------------------------
bgPred :: Index -> ([F.Symbol], F.Pred)
--------------------------------------------------------------------------------
bgPred me = ( bXs , F.pAnd $ [ bp i `F.PIff` bindPred me bP | (i, bP) <- iBps  ]
                          ++ [ bp i `F.PImp` bp i'          | (i, i') <- links ]
            )
  where
   bXs    = bx <$> (sortNub . concatMap (\(x, y) -> [x, y]) $ links)
   iBps   = M.toList (bindExpr me)
   links  = M.toList (bindPrev me)

bindPred :: Index -> BindPred -> F.Pred
bindPred me (BP p kIs) = F.pAnd (p : kIps)
  where
    kIps               = kIndexPred me <$> kIs


kIndexPred :: Index -> KIndex -> F.Pred
kIndexPred me kI = case kIDef of
                     Just cs -> F.pOr (kIndexCube ySu <$> cs)
                     Nothing -> bp kI
  where
    kIDef        = M.lookup k (kvDef me)
    msg          = "kIndexPred: unknown KIndex" ++ show kI
    (k, ySu)     = safeLookup msg kI (kvUse me)

kIndexCube :: F.Subst -> Cube ->  F.Pred
kIndexCube ySu c = bp j &.& (ySu `eqSubst` zSu)
  where
    zSu          = cuSubst c
    j            = cuId    c

eqSubst :: F.Subst -> F.Subst -> F.Pred
eqSubst = error "TBD:substPred"

{-

      kIndexPred kI  = * \/_{j in Js} bp[j] /\ (Y = Z[j])   IF  G[j] |- K[X:=Z[j]] ... <- kvDef k
                       * bp[kI]                             OTHERWISE
                                                            where
                                                              k[X := Y] = kvUse kI

-}

class BitSym a where
  bx :: a -> F.Symbol
  bp :: a -> F.Pred
  bp = F.eVar . bx

instance BitSym KIndex where
  bx = F.suffixSymbol "lq_kindex$" . F.symbol . show

instance BitSym F.BindId where
  bx = F.intSymbol "lq_bind$"

instance BitSym F.SubcId where
  bx = F.intSymbol "lq_cstr$"

instance BitSym BIndex where
  bx (Bind i) = bx i
  bx (Cstr j) = bx j


--------------------------------------------------------------------------------
-- | Flipping on bits for a single SubC, given current Solution ----------------
--------------------------------------------------------------------------------
lhsPred :: Index -> F.SolEnv -> Solution -> F.SimpC a -> F.Expr
--------------------------------------------------------------------------------
lhsPred = error "TBD:lhsPred"


{- | [NOTE: Bit-Indexed Representation]

     The whole constraint system will be represented by a collection
     of bit indexed propositions:

     Definitions:

     * Tree-Pred links are (i, i')
     * BindIds are `i`
     * SubcIds are `j`
     * KIndex  are `kI`
     * KVar    are `k`
     * Substs  are `[X := Y]` where `X` are the KVars params
     * Each BIndex = BindId i | SubcId j is represented by a
       symbol, respectively `bp[i]`, `bp[j]`
     * Solutions are `s`

      bgPred = /\_{i in BindIds} ( bp[i] <=> bindPred i  )
                           /\_{i in prev   } ( bp[i] ==> bp[prev(i)] )

      bindPred i     = p /\_{kI in kIs} kIndexPred kI
        where
          (p, kIs)       = bindExpr i

      kIndexPred kI  = * \/_{j in Js} bp[j] /\ (Y = Z[j])   IF  G[j] |- K[X:=Z[j]] ... <- kvDef k
                       * bp[kI]                             OTHERWISE
                                                            where
                                                              k[X := Y] = kvUse kI

      lhsPred s j    = /\_{kI} bp[kI] <=> kIndexSol s kI

      kIndexSol s kI = s(k) [ X:= Y ]
        where
          k[X := Y]  = kvUse kI
 -}
