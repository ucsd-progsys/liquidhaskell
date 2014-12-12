{-# LANGUAGE TupleSections #-}

module Language.Haskell.Liquid.Bare.RTEnv (
    makeRTEnv
  ) where

import Control.Applicative ((<$>))
import Control.Monad.State
import Data.Graph hiding (Graph)
import Data.Maybe
import Text.PrettyPrint.HughesPJ

import qualified Control.Exception   as Ex
import qualified Data.HashMap.Strict as M

import Language.Fixpoint.Misc (errorstar)
import Language.Fixpoint.Types (Symbol, dummyPos)

import Language.Haskell.Liquid.GhcMisc (sourcePosSrcSpan)
import Language.Haskell.Liquid.Misc (ordNub)
import Language.Haskell.Liquid.Types

import qualified Language.Haskell.Liquid.Measure as Ms

import Language.Haskell.Liquid.Bare.Env
import Language.Haskell.Liquid.Bare.Misc (symbolRTyVar)
import Language.Haskell.Liquid.Bare.Reft
import Language.Haskell.Liquid.Bare.Type

--- Refinement Type Aliases
makeRTEnv specs
  = do forM_ rts $ \(mod, rta) -> setRTAlias (rtName rta) $ Left (mod, rta)
       forM_ pts $ \(mod, pta) -> setRPAlias (rtName pta) $ Left (mod, pta)
       forM_ ets $ \(mod, eta) -> setREAlias (rtName eta) $ Left (mod, eta)
       makeREAliases ets
       makeRPAliases pts
       makeRTAliases rts
    where
       rts = (concat [(m,) <$> Ms.aliases  s | (m, s) <- specs])
       pts = (concat [(m,) <$> Ms.paliases s | (m, s) <- specs])
       ets = (concat [(m,) <$> Ms.ealiases s | (m, s) <- specs])
       
makeRTAliases xts
  = do let aliases = map snd xts
           table   = buildAliasTable aliases
           graph   = buildAliasGraph aliases
       checkCyclicAliases table graph
       mapM_ expBody xts
  where
    expBody (mod,xt) = inModule mod $ do
                             let l = rtPos xt
                             body <- withVArgs l (rtVArgs xt) $ ofBareType l $ rtBody xt
                             setRTAlias (rtName xt) $ Right $ mapRTAVars symbolRTyVar $ xt { rtBody = body }

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


buildAliasTable :: [RTAlias Symbol BareType] -> M.HashMap Symbol (RTAlias Symbol BareType)
buildAliasTable
  = M.fromList . map (\alias -> (rtName alias, alias))


type Graph t = [Node t]
type Node  t = (t, t, [t])


buildAliasGraph :: [RTAlias Symbol BareType] -> Graph Symbol
buildAliasGraph
  = map buildAliasNode

buildAliasNode :: RTAlias Symbol BareType -> Node Symbol
buildAliasNode alias
  = (rtName alias, rtName alias, buildAliasEdges $ rtBody alias)

buildAliasEdges :: BareType -> [Symbol]
buildAliasEdges
  = ordNub . buildAliasEdges'

buildAliasEdges' :: BareType -> [Symbol]
buildAliasEdges' (RApp (Loc _ c) ts rs _)
  = c : concat (map buildAliasEdges' ts ++ map buildAliasEdges' (mapMaybe go rs))
  where
    go (RPropP _ _) = Nothing
    go (RProp  _ t) = Just t
    go (RHProp _ _) = errorstar "TODO:EFFECTS:buildAliasEdges'"
buildAliasEdges' (RVar _ _)
  = []
buildAliasEdges' (RFun _ t1 t2 _)
  = buildAliasEdges' t1 ++ buildAliasEdges' t2
buildAliasEdges' (RAppTy t1 t2 _)
  = buildAliasEdges' t1 ++ buildAliasEdges' t2
buildAliasEdges' (RAllE _ t1 t2)
  = buildAliasEdges' t1 ++ buildAliasEdges' t2
buildAliasEdges' (REx _ t1 t2)
  = buildAliasEdges' t1 ++ buildAliasEdges' t2
buildAliasEdges' (RAllT _ t)
  = buildAliasEdges' t
buildAliasEdges' (RAllP _ t)
  = buildAliasEdges' t
buildAliasEdges' (RAllS _ t)
  = buildAliasEdges' t
buildAliasEdges' (ROth _)
  = []
buildAliasEdges' (RExprArg _)
  = []
buildAliasEdges' (RHole _)
  = []


checkCyclicAliases :: M.HashMap Symbol (RTAlias Symbol BareType) -> Graph Symbol -> BareM ()
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

    locate sym
      = case M.lookup sym table of
          Nothing ->
            errorstar $ "checkCyclicAliases: Dangling alias symbol: " ++ show sym
          Just alias ->
            (sourcePosSrcSpan $ rtPos alias, pprint sym)

