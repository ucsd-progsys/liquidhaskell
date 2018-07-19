{-# LANGUAGE TupleSections #-}

module Language.Haskell.Liquid.Bare.Expand 
  ( -- * Create alias expansion environment
    makeRTEnv 
    -- * Use alias expansion 
  , Expand (..)
  ) where

import Prelude hiding (error)

import Data.Graph hiding (Graph)
import Data.Maybe

import qualified Control.Exception   as Ex
import qualified Data.HashMap.Strict as M
import qualified Data.List           as L

import qualified Language.Fixpoint.Types as F 
import           Language.Fixpoint.Misc (fst3)
import           Language.Fixpoint.Types (Expr(..), Symbol, symbol) -- , tracepp)
import qualified Language.Haskell.Liquid.GHC.Misc as GM -- (fSrcSpan) -- , sourcePosSrcSpan)
import           Language.Haskell.Liquid.Types.RefType (symbolRTyVar)
-- import           Language.Haskell.Liquid.Types.Fresh
import           Language.Haskell.Liquid.Types
import qualified Language.Haskell.Liquid.Measure      as Ms
import qualified Language.Haskell.Liquid.Bare.Resolve as Bare
import qualified Language.Haskell.Liquid.Bare.Types   as Bare

-- import           Language.Haskell.Liquid.Bare.Env
-- import           Language.Haskell.Liquid.Bare.Expand
-- import           Language.Haskell.Liquid.Bare.OfType

--------------------------------------------------------------------------------
-- | `makeRTEnv` initializes the env needed to `expand` refinements and types,
--   that is, the below needs to be called *before* we use `Expand.expand`
--------------------------------------------------------------------------------
makeRTEnv :: Bare.Env -> ModName -> Ms.BareSpec -> [(ModName, Ms.BareSpec)] -> LogicMap 
          -> SpecRTEnv 
--------------------------------------------------------------------------------
makeRTEnv env m lfSpec specs lmap = makeRTAliases (makeREAliases eAs) tAs  
  where
    tAs   = [ specRTAlias env m t | (m, s) <- specs, t <- Ms.aliases  s ]
    eAs   = [ specREAlias env m e | (m, s) <- specs, e <- Ms.ealiases s ]
         ++ [ specREAlias env m e | e      <- Ms.ealiases lfSpec        ]                        
         ++ [ specREAlias env m e | (_, xl) <- M.toList (lmSymDefs lmap)
                                  , let e = lmapEAlias xl               ]

makeREAliases :: [Located (RTAlias Symbol Expr)] -> SpecRTEnv 
makeREAliases = graphExpand buildExprEdges f mempty 
  where
    f rtEnv xt = setREAlias rtEnv (expand rtEnv xt)

makeRTAliases :: SpecRTEnv -> [Located (RTAlias RTyVar SpecType)] -> SpecRTEnv  
makeRTAliases rte lxts = graphExpand buildTypeEdges f rte lxts 
  where
    f rtEnv xt         = setRTAlias rtEnv (expand rtEnv xt)
 
specRTAlias :: Bare.Env -> ModName -> Located (RTAlias Symbol BareType) -> Located (RTAlias RTyVar SpecType) 
specRTAlias env m la = F.atLoc la $ RTA 
  { rtName  = rtName a
  , rtTArgs = symbolRTyVar <$> rtTArgs a
  , rtVArgs = rtVArgs a 
  , rtBody  = F.val (ofBareType env m (F.atLoc la (rtBody a))) 
  } 
  where a   = val la 

specREAlias :: Bare.Env -> ModName -> Located (RTAlias Symbol Expr) -> Located (RTAlias Symbol Expr) 
specREAlias env m la = F.atLoc la $ a { rtBody = F.val (ofBareExpr env m (F.atLoc la (rtBody a))) } 
  where 
    a     = val la 


graphExpand :: (PPrint t)
            => (AliasTable x t -> t -> [Symbol])         -- ^ dependencies
            -> (thing -> Located (RTAlias x t) -> thing) -- ^ update
            -> thing                                     -- ^ initial
            -> [Located (RTAlias x t)]                   -- ^ vertices
            -> thing                                     -- ^ final 
graphExpand buildEdges expBody env lxts 
           = L.foldl' expBody env (genExpandOrder table' graph)
  where 
    -- xts    = val <$> lxts
    table  = buildAliasTable lxts
    graph  = buildAliasGraph (buildEdges table) lxts
    table' = checkCyclicAliases table graph

setRTAlias :: SpecRTEnv -> Located (RTAlias RTyVar SpecType) -> SpecRTEnv 
setRTAlias env a = env { typeAliases =  M.insert n a (typeAliases env) } 
  where 
    n            = rtName (val a)  


setREAlias :: SpecRTEnv -> Located (RTAlias Symbol Expr) -> SpecRTEnv 
setREAlias env a = env { exprAliases = M.insert n a (exprAliases env) } 
  where 
    n            = rtName (val a)



--------------------------------------------------------------------------------
type AliasTable x t = M.HashMap Symbol (Located (RTAlias x t))

buildAliasTable :: [Located (RTAlias x t)] -> AliasTable x t
buildAliasTable = M.fromList . map (\rta -> (rtName (val rta), rta))

fromAliasSymbol :: AliasTable x t -> Symbol -> Located (RTAlias x t)
fromAliasSymbol table sym
  = fromMaybe err (M.lookup sym table)
  where
    err = panic Nothing $ "fromAliasSymbol: Dangling alias symbol: " ++ show sym

type Graph t = [Node t]
type Node  t = (t, t, [t])

buildAliasGraph :: (PPrint t) => (t -> [Symbol]) -> [Located (RTAlias x t)] 
                -> Graph Symbol
buildAliasGraph buildEdges = map (buildAliasNode buildEdges)

buildAliasNode :: (PPrint t) => (t -> [Symbol]) -> Located (RTAlias x t) 
               -> Node Symbol
buildAliasNode f la = (rtName a, rtName a, f (rtBody a))
  where 
    a               = val la 

checkCyclicAliases :: AliasTable x t -> Graph Symbol -> AliasTable x t 
checkCyclicAliases table graph
  = case mapMaybe go (stronglyConnComp graph) of
      []   -> table 
      sccs -> Ex.throw (cycleAliasErr table <$> sccs)
    where
      go (CyclicSCC vs) = Just vs
      go (AcyclicSCC _) = Nothing

cycleAliasErr :: AliasTable x t -> [Symbol] -> Error
cycleAliasErr _ []          = panic Nothing "checkCyclicAliases: No type aliases in reported cycle"
cycleAliasErr t scc@(rta:_) = ErrAliasCycle { pos    = fst (locate rta)
                                            , acycle = map locate scc }
  where
    locate sym = ( GM.fSrcSpan $ fromAliasSymbol t sym
                 , pprint sym )


genExpandOrder :: AliasTable x t -> Graph Symbol -> [Located (RTAlias x t)]
genExpandOrder table graph
  = map (fromAliasSymbol table) symOrder
  where
    (digraph, lookupVertex, _)
      = graphFromEdges graph
    symOrder
      = map (fst3 . lookupVertex) $ reverse $ topSort digraph

--------------------------------------------------------------------------------

ordNub :: Ord a => [a] -> [a]
ordNub = map head . L.group . L.sort

buildTypeEdges :: AliasTable x SpecType -> SpecType -> [Symbol]
buildTypeEdges table = ordNub . go
  where
    go :: SpecType -> [Symbol]
    go (RApp c ts rs _) = go_alias (symbol c) ++ concatMap go ts ++ concatMap go (mapMaybe go_ref rs)
    go (RImpF _ t1 t2 _) = go t1 ++ go t2
    go (RFun _ t1 t2 _) = go t1 ++ go t2
    go (RAppTy t1 t2 _) = go t1 ++ go t2
    go (RAllE _ t1 t2)  = go t1 ++ go t2
    go (REx _ t1 t2)    = go t1 ++ go t2
    go (RAllT _ t)      = go t
    go (RAllP _ t)      = go t
    go (RAllS _ t)      = go t
    go (RVar _ _)       = []
    go (RExprArg _)     = []
    go (RHole _)        = []
    go (RRTy env _ _ t) = concatMap (go . snd) env ++ go t
    go_alias c          = [c | M.member c table]
    go_ref (RProp _ (RHole _)) = Nothing
    go_ref (RProp  _ t) = Just t


buildExprEdges :: M.HashMap Symbol a -> Expr -> [Symbol]
buildExprEdges table  = ordNub . go
  where
    go :: Expr -> [Symbol]
    go (EApp e1 e2)   = go e1 ++ go e2
    go (ENeg e)       = go e
    go (EBin _ e1 e2) = go e1 ++ go e2
    go (EIte _ e1 e2) = go e1 ++ go e2
    go (ECst e _)     = go e
    go (ESym _)       = []
    go (ECon _)       = []
    go (EVar v)       = go_alias v
    go (PAnd ps)       = concatMap go ps
    go (POr ps)        = concatMap go ps
    go (PNot p)        = go p
    go (PImp p q)      = go p ++ go q
    go (PIff p q)      = go p ++ go q
    go (PAll _ p)      = go p
    go (ELam _ e)      = go e
    go (ECoerc _ _ e)  = go e
    go (PAtom _ e1 e2) = go e1 ++ go e2
    go (ETApp e _)     = go e
    go (ETAbs e _)     = go e
    go (PKVar _ _)     = []
    go (PExist _ e)    = go e
    go (PGrad _ _ _ e) = go e
    go_alias f         = [f | M.member f table ]


----------------------------------------------------------------------------------
-- | Using the `SpecRTEnv` to do alias-expansion 
----------------------------------------------------------------------------------
class Expand a where 
  expand :: SpecRTEnv -> a -> a 

----------------------------------------------------------------------------------
