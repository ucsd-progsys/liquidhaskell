{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE OverloadedStrings #-}

-- | This module a test for whether the constraint dependencies form a
--   reducible graph.

module Language.Fixpoint.Graph.Reducible ( isReducible ) where

import qualified Data.Tree                            as T
import qualified Data.HashMap.Strict                  as M
import           Data.Graph.Inductive

import           Language.Fixpoint.Misc         -- hiding (group)
import qualified Language.Fixpoint.Types.Visitor      as V
import qualified Language.Fixpoint.Types              as F


--------------------------------------------------------------------------------
isReducible :: (F.TaggedC c a) => F.GInfo c a -> Bool
--------------------------------------------------------------------------------
isReducible fi = all (isReducibleWithStart g) vs
  where
    g  = convertToGraph fi
    vs = {- trace (showDot $ fglToDotGeneric g show (const "") id) -} nodes g

isReducibleWithStart :: Gr a b -> Node -> Bool
isReducibleWithStart g x = all (isBackEdge domList) rEdges
  where
    dfsTree              = head $ dff [x] g --head because only care about nodes reachable from 'start node'?
    rEdges               = [ e | e@(a,b) <- edges g, isDescendant a b dfsTree]
    domList              = dom g x



convertToGraph :: (F.TaggedC c a) => F.GInfo c a -> Gr Int ()
convertToGraph fi = mkGraph vs es
  where
    subCs        = M.elems (F.cm fi)
    es           = lUEdge <$> concatMap (subcEdges' kvI $ F.bs fi) subCs
    ks           = M.keys (F.ws fi)
    kiM          = M.fromList $ zip ks [0..]
    kvI k        = safeLookup ("convertToGraph: " ++ show k) k kiM
    vs           = lNode . kvI <$> M.keys (F.ws fi)
    lNode i      = (i, i)
    lUEdge (i,j) = (i, j, ())

isDescendant :: Node -> Node -> T.Tree Node -> Bool
isDescendant x y (T.Node z f) | z == y    = f `contains` x
                              | z == x    = False
                              | otherwise = any (isDescendant x y) f

contains :: [T.Tree Node] -> Node -> Bool
contains t x = x `elem` concatMap T.flatten t

isBackEdge :: [(Node, [Node])] -> Edge -> Bool
isBackEdge t (u,v) = v `elem` xs
  where
    (Just xs) = lookup u t

subcEdges' :: (F.TaggedC c a) => (F.KVar -> Node) -> F.BindEnv -> c a -> [(Node, Node)]
subcEdges' kvI be c = [(kvI k1, kvI k2) | k1 <- V.envKVars be c
                                        , k2 <- V.kvars $ F.crhs c]
