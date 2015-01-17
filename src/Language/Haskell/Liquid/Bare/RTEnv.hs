{-# LANGUAGE TupleSections #-}

module Language.Haskell.Liquid.Bare.RTEnv (
    makeRTEnv
  ) where

import Control.Applicative ((<$>))
import Control.Monad.State
import Data.Graph hiding (Graph)
import Data.Maybe

import qualified Control.Exception   as Ex
import qualified Data.HashMap.Strict as M

import Language.Fixpoint.Misc (errorstar, fst3)
import Language.Fixpoint.Types (Symbol)

import Language.Haskell.Liquid.GhcMisc (sourcePosSrcSpan)
import Language.Haskell.Liquid.Misc (ordNub)
import Language.Haskell.Liquid.RefType (symbolRTyVar)
import Language.Haskell.Liquid.Types

import qualified Language.Haskell.Liquid.Measure as Ms

import Language.Haskell.Liquid.Bare.Env
import Language.Haskell.Liquid.Bare.Expand
import Language.Haskell.Liquid.Bare.OfType

--- Refinement Type Aliases
makeRTEnv specs
  = do forM_ pts $ \(mod, pta) -> setRPAlias (rtName pta) $ Left (mod, pta)
       forM_ ets $ \(mod, eta) -> setREAlias (rtName eta) $ Left (mod, eta)
       makeREAliases ets
       makeRPAliases pts
       makeRTAliases rts
    where
       rts = (concat [(m,) <$> Ms.aliases  s | (m, s) <- specs])
       pts = (concat [(m,) <$> Ms.paliases s | (m, s) <- specs])
       ets = (concat [(m,) <$> Ms.ealiases s | (m, s) <- specs])

makeRTAliases xts
  = do let table   = buildAliasTable xts
           graph   = buildAliasGraph table $ map snd xts
       checkCyclicAliases table graph

       let ordered = genExpandOrder table graph
       mapM_ expBody ordered
  where
    expBody (mod,xt) = inModule mod $ do
                             let l = rtPos xt
                             body <- withVArgs l (rtVArgs xt) $ ofBareType l $ rtBody xt
                             setRTAlias (rtName xt) $ mapRTAVars symbolRTyVar $ xt { rtBody = body }

makeRPAliases xts     = mapM_ expBody xts
  where 
    expBody (mod, xt) = inModule mod $ do
                          let l = rtPos xt
                          body <- withVArgs l (rtVArgs xt) $ expandPred l $ rtBody xt
                          setRPAlias (rtName xt) $ Right $ xt { rtBody = body }

makeREAliases xts     = mapM_ expBody xts
  where 
    expBody (mod, xt) = inModule mod $ do
                          let l = rtPos xt
                          body <- withVArgs l (rtVArgs xt) $ expandExpr l $ rtBody xt
                          setREAlias (rtName xt) $ Right $ xt { rtBody = body }

type AliasTable = M.HashMap Symbol (ModName, RTAlias Symbol BareType)

buildAliasTable :: [(ModName, RTAlias Symbol BareType)] -> AliasTable
buildAliasTable
  = M.fromList . map (\(mod, rta) -> (rtName rta, (mod, rta)))

fromAliasSymbol :: AliasTable -> Symbol -> (ModName, RTAlias Symbol BareType)
fromAliasSymbol table sym
  = fromMaybe err $ M.lookup sym table
  where
    err = errorstar $ "fromAliasSymbol: Dangling alias symbol: " ++ show sym


type Graph t = [Node t]
type Node  t = (t, t, [t])

buildAliasGraph :: AliasTable -> [RTAlias Symbol BareType] -> Graph Symbol
buildAliasGraph table
  = map (buildAliasNode table)

buildAliasNode :: AliasTable -> RTAlias Symbol BareType -> Node Symbol
buildAliasNode table alias
  = (rtName alias, rtName alias, buildAliasEdges table $ rtBody alias)

buildAliasEdges :: AliasTable -> BareType -> [Symbol]
buildAliasEdges table
  = ordNub . go
  where go :: BareType -> [Symbol]
        go (RApp (Loc _ c) ts rs _)
          = go_alias c ++ concat (map go ts ++ map go (mapMaybe go_ref rs))

        go (RFun _ t1 t2 _)
          = go t1 ++ go t2
        go (RAppTy t1 t2 _)
          = go t1 ++ go t2
        go (RAllE _ t1 t2)
          = go t1 ++ go t2
        go (REx _ t1 t2)
          = go t1 ++ go t2
        go (RAllT _ t)
          = go t
        go (RAllP _ t)
          = go t
        go (RAllS _ t)
          = go t

        go (RVar _ _)
          = []
        go (ROth _)
          = []
        go (RExprArg _)
          = []
        go (RHole _)
          = []

        go (RRTy env _ _ t)
          = concatMap (go . snd) env ++ go t

        go_alias c
          = case M.lookup c table of
              Just _  -> [c]
              Nothing -> [ ]

        go_ref (RPropP _ _) = Nothing
        go_ref (RProp  _ t) = Just t
        go_ref (RHProp _ _) = errorstar "TODO:EFFECTS:buildAliasEdges"


checkCyclicAliases :: AliasTable -> Graph Symbol -> BareM ()
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


genExpandOrder :: AliasTable -> Graph Symbol -> [(ModName, RTAlias Symbol BareType)]
genExpandOrder table graph 
  = map (fromAliasSymbol table) symOrder
  where
    (digraph, lookupVertex, _)
      = graphFromEdges graph
    symOrder
      = map (fst3 . lookupVertex) $ reverse $ topSort digraph

