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

import Language.Fixpoint.Misc (errorstar, fst3)
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
  = do let table   = buildAliasTable xts
           graph   = buildAliasGraph table $ map snd xts
       checkCyclicAliases table graph

       let ordered = genExpandOrder table graph
       mapM_ expBody ordered
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

type AliasTable = M.HashMap Symbol (ModName, RTAlias Symbol BareType)

buildAliasTable :: [(ModName, RTAlias Symbol BareType)] -> AliasTable
buildAliasTable
  = M.fromList . map (\(mod, rta) -> (rtName rta, (mod, rta)))


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
  where go (RApp (Loc _ c) ts rs _)
          = curr ++ concat (map go ts ++ map go (mapMaybe ref rs))
          where
            curr 
              = case M.lookup c table of
                  Nothing -> [ ]
                  Just _  -> [c]

            ref (RPropP _ _) = Nothing
            ref (RProp  _ t) = Just t
            ref (RHProp _ _) = errorstar "TODO:EFFECTS:buildAliasEdges"

        go (RVar _ _)
          = []
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
        go (ROth _)
          = []
        go (RExprArg _)
          = []
        go (RHole _)
          = []


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

    locate sym
      = case M.lookup sym table of
          Nothing ->
            errorstar $ "checkCyclicAliases: Dangling alias symbol: " ++ show sym
          Just (_, alias) ->
            (sourcePosSrcSpan $ rtPos alias, pprint sym)


genExpandOrder :: AliasTable -> Graph Symbol -> [(ModName, RTAlias Symbol BareType)]
genExpandOrder table graph 
  = map (fromJust . flip M.lookup table) $ traceShow "symOrder: " symOrder
  where
    (digraph, lookupVertex, _)
      = graphFromEdges graph
    symOrder
      = map (fst3 . lookupVertex) $ reverse $ topSort digraph

