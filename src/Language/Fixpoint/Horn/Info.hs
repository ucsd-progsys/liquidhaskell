{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveTraversable          #-}

module Language.Fixpoint.Horn.Info (
    hornFInfo
  ) where

import qualified Data.HashMap.Strict            as M
import qualified Data.List                      as L
import qualified Data.Tuple                     as Tuple
import qualified Data.Maybe                     as Mb
import           Data.Either                    (partitionEithers)
import           GHC.Generics                   (Generic)
import qualified Language.Fixpoint.Misc         as Misc
import qualified Language.Fixpoint.Types        as F
import qualified Language.Fixpoint.Types.Config as F
import qualified Language.Fixpoint.Horn.Types   as H

hornFInfo :: F.Config -> H.Query a -> F.FInfo a
hornFInfo cfg q = mempty
  { F.cm        = cs
  , F.bs        = be2
  , F.ebinds    = ebs
  , F.ws        = kvEnvWfCs kve
  , F.quals     = H.qQuals q
  , F.gLits     = F.fromMapSEnv $ H.qCon q
  , F.dLits     = F.fromMapSEnv $ H.qDis q
  , F.ae        = axEnv cfg q cs
  , F.ddecls    = H.qData q
  }
  where
    be0         = F.emptyBindEnv
    (be1, kve)  = hornWfs   be0     (H.qVars q)
    (be2, ebs, cs) = hornSubCs be1 kve hCst
    hCst           = H.qCstr q

axEnv :: F.Config -> H.Query a -> M.HashMap F.SubcId b -> F.AxiomEnv 
axEnv cfg q cs = mempty 
  { F.aenvEqs    = H.qEqns q
  , F.aenvSimpl  = H.qMats q
  , F.aenvExpand = if F.rewriteAxioms cfg then const True <$> cs else mempty
  } 

----------------------------------------------------------------------------------
hornSubCs :: F.BindEnv -> KVEnv a -> H.Cstr a
          -> (F.BindEnv, [F.BindId], M.HashMap F.SubcId (F.SubC a))
----------------------------------------------------------------------------------
hornSubCs be kve c = (be', ebs, M.fromList (F.addIds cs))
  where
    (be', ebs, cs)      = goS kve F.emptyIBindEnv lhs0 be c
    lhs0           = bindSortedReft kve H.dummyBind

-- | @goS@ recursively traverses the NNF constraint to build up a list
--   of the vanilla @SubC@ constraints.

goS :: KVEnv a -> F.IBindEnv -> F.SortedReft -> F.BindEnv -> H.Cstr a
    -> (F.BindEnv, [F.BindId], [F.SubC a])

goS kve env lhs be c = (be', mEbs, subcs)
  where
    (be', ecs) = goS' kve env lhs be c
    (mEbs, subcs) = partitionEithers ecs

goS' :: KVEnv a -> F.IBindEnv -> F.SortedReft -> F.BindEnv -> H.Cstr a
    -> (F.BindEnv, [Either F.BindId (F.SubC a)])
goS' kve env lhs be (H.Head p l) = (be, [Right subc])
  where
    subc                        = F.mkSubC env lhs rhs Nothing [] l
    rhs                         = updSortedReft kve lhs p

goS' kve env lhs be (H.CAnd cs)  = (be', concat subcss)
  where
    (be', subcss)               = L.mapAccumL (goS' kve env lhs) be cs

goS' kve env _   be (H.All b c)  = (be'', subcs)
  where
    (be'', subcs)               = goS' kve env' bSR be' c
    (bId, be')                  = F.insertBindEnv (H.bSym b) bSR be
    bSR                         = bindSortedReft kve b
    env'                        = F.insertsIBindEnv [bId] env

goS' kve env _   be (H.Any b c)  = (be'', Left bId : subcs)
  where
    (be'', subcs)               = goS' kve env' bSR be' c
    (bId, be')                  = F.insertBindEnv (H.bSym b) bSR be
    bSR                         = bindSortedReft kve b
    env'                        = F.insertsIBindEnv [bId] env

bindSortedReft :: KVEnv a -> H.Bind -> F.SortedReft
bindSortedReft kve (H.Bind x t p) = F.RR t (F.Reft (x, predExpr kve p))

updSortedReft :: KVEnv a -> F.SortedReft -> H.Pred -> F.SortedReft
updSortedReft kve (F.RR s (F.Reft (v, _))) p = F.RR s (F.Reft (v, predExpr kve p))

predExpr :: KVEnv a -> H.Pred -> F.Expr
predExpr kve        = go
  where
    go (H.Reft  e ) = e
    go (H.Var k ys) = kvApp kve k ys
    go (H.PAnd  ps) = F.PAnd (go <$> ps)

kvApp :: KVEnv a -> F.Symbol -> [F.Symbol] -> F.Expr
kvApp kve k ys = F.PKVar (F.KV k) su
  where
    su         = F.mkSubst (zip params (F.eVar <$> ys))
    params     = Mb.fromMaybe err1 $ kvParams <$> M.lookup k kve
    err1       = F.panic ("Unknown Horn variable: " ++ F.showpp k)

----------------------------------------------------------------------------------
hornWfs :: F.BindEnv -> [H.Var a] -> (F.BindEnv, KVEnv a)
----------------------------------------------------------------------------------
hornWfs be vars = (be', kve)
  where
    kve         = M.fromList [ (kname i, i) | i <- is ]
    (be', is)   = L.mapAccumL kvInfo be vars
    kname       = H.hvName . kvVar

kvInfo :: F.BindEnv -> H.Var a -> (F.BindEnv, KVInfo a)
kvInfo be k       = (be', KVInfo k (fst <$> xts) wfc)
  where
    -- make the WfC
    wfc           = F.WfC wenv wrft  (H.hvMeta k)
    wenv          = F.fromListIBindEnv ids
    wrft          = (x, t, F.KV (H.hvName k))
    -- add the binders
    (be', ids)    = L.mapAccumL insertBE be xts'
    ((x,t), xts') = Misc.safeUncons "Horn var with no args" xts
    -- make the parameters
    xts           = [ (hvarArg k i, t) | (t, i) <- zip (H.hvArgs k) [0..] ]

insertBE :: F.BindEnv -> (F.Symbol, F.Sort) -> (F.BindEnv, F.BindId)
insertBE be (x, t) = Tuple.swap $ F.insertBindEnv x (F.trueSortedReft t) be

----------------------------------------------------------------------------------
-- | Data types and helpers for manipulating information about KVars
----------------------------------------------------------------------------------
type KVEnv a  = M.HashMap F.Symbol (KVInfo a)

data KVInfo a = KVInfo
  { kvVar    :: !(H.Var a)
  , kvParams :: ![F.Symbol]
  , kvWfC    :: !(F.WfC a)
  }
  deriving (Generic, Functor)

kvEnvWfCs :: KVEnv a -> M.HashMap F.KVar (F.WfC a)
kvEnvWfCs kve = M.fromList [ (F.KV k, kvWfC info) | (k, info) <- M.toList kve ]

hvarArg :: H.Var a -> Int -> F.Symbol
hvarArg k i = F.intSymbol (F.suffixSymbol hvarPrefix (H.hvName k)) i

hvarPrefix :: F.Symbol
hvarPrefix = F.symbol "nnf_arg"
