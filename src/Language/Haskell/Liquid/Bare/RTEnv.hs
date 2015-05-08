{-# LANGUAGE TupleSections #-}

module Language.Haskell.Liquid.Bare.RTEnv (
    makeRTEnv
  ) where

import Control.Applicative ((<$>))
import Data.Graph hiding (Graph)
import Data.Maybe

import qualified Control.Exception   as Ex
import qualified Data.HashMap.Strict as M

import Language.Fixpoint.Misc (errorstar, fst3)
import Language.Fixpoint.Types (Expr(..), Pred(..), Symbol)

import Language.Haskell.Liquid.GhcMisc (sourcePosSrcSpan)
import Language.Haskell.Liquid.Misc (ordNub)
import Language.Haskell.Liquid.RefType (symbolRTyVar)
import Language.Haskell.Liquid.Types

import qualified Language.Haskell.Liquid.Measure as Ms

import Language.Haskell.Liquid.Bare.Env
import Language.Haskell.Liquid.Bare.Expand
import Language.Haskell.Liquid.Bare.OfType
import Language.Haskell.Liquid.Bare.Resolve

--------------------------------------------------------------------------------

makeRTEnv specs
  = do makeREAliases ets
       makeRPAliases pts
       makeRTAliases rts
    where
       rts = (concat [(m,) <$> Ms.aliases  s | (m, s) <- specs])
       pts = (concat [(m,) <$> Ms.paliases s | (m, s) <- specs])
       ets = (concat [(m,) <$> Ms.ealiases s | (m, s) <- specs])


makeRTAliases
  = graphExpand buildTypeEdges expBody
  where
    expBody (mod, xt)
      = inModule mod $
          do let l  = rtPos  xt
             let l' = rtPosE xt
             body  <- withVArgs l l' (rtVArgs xt) $ ofBareType l $ rtBody xt
             setRTAlias (rtName xt) $ mapRTAVars symbolRTyVar $ xt { rtBody = body}

makeRPAliases
  = graphExpand buildPredEdges expBody
  where
    expBody (mod, xt)
      = inModule mod $
          do let l  = rtPos  xt
             let l' = rtPosE xt
             body  <- withVArgs l l' (rtVArgs xt) $ resolve l =<< (expandPred $ rtBody xt)
             setRPAlias (rtName xt) $ xt { rtBody = body }

makeREAliases
  = graphExpand buildExprEdges expBody
  where
    expBody (mod, xt)
      = inModule mod $
          do let l  = rtPos  xt
             let l' = rtPosE xt
             body  <- withVArgs l l' (rtVArgs xt) $ resolve l =<< (expandExpr $ rtBody xt)
             setREAlias (rtName xt) $ xt { rtBody = body }


graphExpand buildEdges expBody xts
  = do let table = buildAliasTable xts
           graph = buildAliasGraph (buildEdges table) (map snd xts)
       checkCyclicAliases table graph

       mapM_ expBody $ genExpandOrder table graph

--------------------------------------------------------------------------------

type AliasTable t = M.HashMap Symbol (ModName, RTAlias Symbol t)

buildAliasTable :: [(ModName, RTAlias Symbol t)] -> AliasTable t
buildAliasTable
  = M.fromList . map (\(mod, rta) -> (rtName rta, (mod, rta)))

fromAliasSymbol :: AliasTable t -> Symbol -> (ModName, RTAlias Symbol t)
fromAliasSymbol table sym
  = fromMaybe err $ M.lookup sym table
  where
    err = errorstar $ "fromAliasSymbol: Dangling alias symbol: " ++ show sym


type Graph t = [Node t]
type Node  t = (t, t, [t])

buildAliasGraph :: (t -> [Symbol]) -> [RTAlias Symbol t] -> Graph Symbol
buildAliasGraph buildEdges
  = map (buildAliasNode buildEdges)

buildAliasNode :: (t -> [Symbol]) -> RTAlias Symbol t -> Node Symbol
buildAliasNode buildEdges alias
  = (rtName alias, rtName alias, buildEdges $ rtBody alias)


checkCyclicAliases :: AliasTable t -> Graph Symbol -> BareM ()
checkCyclicAliases table graph
  = case mapMaybe go $ stronglyConnComp graph of
      [] ->
        return ()
      sccs ->
        Ex.throw $ map err sccs
  where
    go (AcyclicSCC _)
      = Nothing
    go (CyclicSCC vs)
      = Just vs

    err :: [Symbol] -> Error
    err scc@(rta:_)
      = ErrAliasCycle { pos    = fst $ locate rta
                      , acycle = map locate scc
                      }
    err []
      = errorstar "Bare.RTEnv.checkCyclicAliases: No type aliases in reported cycle"

    locate sym
      = ( sourcePosSrcSpan $ rtPos $ snd $ fromAliasSymbol table sym
        , pprint sym
        )


genExpandOrder :: AliasTable t -> Graph Symbol -> [(ModName, RTAlias Symbol t)]
genExpandOrder table graph
  = map (fromAliasSymbol table) symOrder
  where
    (digraph, lookupVertex, _)
      = graphFromEdges graph
    symOrder
      = map (fst3 . lookupVertex) $ reverse $ topSort digraph

--------------------------------------------------------------------------------

buildTypeEdges :: AliasTable BareType -> BareType -> [Symbol]
buildTypeEdges table = ordNub . go
  where
    go :: BareType -> [Symbol]
    go (RApp c ts rs _) = go_alias (val c) ++ concatMap go ts ++ concatMap go (mapMaybe go_ref rs)
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
    -- case M.lookup c table of
    --                         Just _  -> [c]
    --                         Nothing -> [ ]

    go_ref (RPropP _ _) = Nothing
    go_ref (RProp  _ t) = Just t
    go_ref (RHProp _ _) = errorstar "TODO:EFFECTS:buildTypeEdges"

buildPredEdges :: AliasTable Pred -> Pred -> [Symbol]
buildPredEdges table = ordNub . go
  where
    go :: Pred -> [Symbol]
    go (PBexp (EApp lf _)) = [ f | let f = val lf, M.member f table]
    go (PAnd ps)           = concatMap go ps
    go (POr ps)            = concatMap go ps
    go (PNot p)            = go p
    go (PImp p q)          = go p ++ go q
    go (PIff p q)          = go p ++ go q
    go (PAll _ p)          = go p
    go _                   = []

    -- go (PBexp _)           = []
    -- go (PAtom _ _ _)       = []
    -- go PTrue               = []
    -- go PFalse              = []
    -- go PTop                = []

buildExprEdges table  = ordNub . go
  where
    go :: Expr -> [Symbol]
    go (EApp lf es)   = go_alias (val lf) ++ concatMap go es
    go (ENeg e)       = go e
    go (EBin _ e1 e2) = go e1 ++ go e2
    go (EIte _ e1 e2) = go e1 ++ go e2
    go (ECst e _)     = go e
    go _              = []

    -- go (ELit _ _)     = []
    -- go (ESym _)       = []
    -- go (ECon _)       = []
    -- go (EVar _)       = []
    -- go EBot           = []

    go_alias f           = [f | M.member f table ]
    --   = case M.lookup f table of
    --       Just _  -> [f]
    --       Nothing -> [ ]
