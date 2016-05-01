--------------------------------------------------------------------------------
-- | This module implements Indexed KV Graphs,
--   a representation of the KVGraph with a fast
--   succ, pred lookup
--------------------------------------------------------------------------------

{-# LANGUAGE OverloadedStrings #-}

module Language.Fixpoint.Graph.Indexed (
  -- * (Abstract) Indexed Graphs
    IKVGraph (..)

  -- * Constructor
  , edgesIkvg

  -- * Destructor
  , ikvgEdges

  -- * Modify
  , addLinks
  , delNodes

  -- * Lookup
  , getSuccs
  , getPreds
  ) where

import           Language.Fixpoint.Graph.Types
import qualified Data.HashSet              as S
import qualified Data.HashMap.Strict       as M
import qualified Data.List as L
import           Data.Hashable (Hashable)

--------------------------------------------------------------------------------
-- | `IKVGraph` is representation of the KVGraph with a fast succ, pred lookup
--------------------------------------------------------------------------------

data IKVGraph = IKVGraph
  { igSucc :: !(M.HashMap CVertex (S.HashSet CVertex))  -- ^ out-edges of a `CVertex`
  , igPred :: !(M.HashMap CVertex (S.HashSet CVertex))  -- ^ in-edges  of a `CVertex`
  } deriving (Show)


addLinks :: IKVGraph -> [CEdge] -> IKVGraph
addLinks = L.foldl' addLink

addLink :: IKVGraph -> CEdge -> IKVGraph
addLink g (u, v) = addSucc (u, v) . addPred (u, v) $ g

delNodes :: IKVGraph -> [CVertex] -> IKVGraph
delNodes = L.foldl' delNode

delNode :: IKVGraph -> CVertex -> IKVGraph
delNode g v = delVtx v . txMany delSucc uvs . txMany delPred vws $ g
  where
    uvs     = [ (u, v) | u <- getPreds g v ]
    vws     = [ (v, w) | w <- getSuccs g v ]

edgesIkvg :: [CEdge] -> IKVGraph
edgesIkvg = addLinks empty

ikvgEdges :: IKVGraph -> [CEdge]
ikvgEdges g = [ (u, v) | (u, vs) <- M.toList (igSucc g), v <- S.toList vs]

getSuccs :: IKVGraph -> CVertex -> [CVertex]
getSuccs g u = S.toList $ M.lookupDefault S.empty u (igSucc g)

getPreds :: IKVGraph -> CVertex -> [CVertex]
getPreds g v = S.toList $ M.lookupDefault S.empty v (igPred g)

--------------------------------------------------------------------------------
empty :: IKVGraph
empty = IKVGraph M.empty M.empty

txMany :: (a -> b -> b) -> [a] -> b -> b
txMany op es g = L.foldl' (flip op) g es

addSucc :: CEdge -> IKVGraph -> IKVGraph
addSucc (u, v) g = g { igSucc = inserts u v (igSucc g) }

addPred :: CEdge -> IKVGraph -> IKVGraph
addPred (u, v) g = g { igPred = inserts v u (igPred g) }

delSucc :: CEdge -> IKVGraph -> IKVGraph
delSucc (u, v) g = g { igSucc = removes u v (igSucc g)}

delPred :: (CVertex, CVertex) -> IKVGraph -> IKVGraph
delPred (u, v) g = g { igPred = removes v u (igPred g)}

delVtx :: CVertex -> IKVGraph -> IKVGraph
delVtx v g = g { igSucc = M.delete v (igSucc g) }
               { igPred = M.delete v (igPred g) }

inserts :: (Eq k, Eq v, Hashable k, Hashable v)
        => k -> v -> M.HashMap k (S.HashSet v) -> M.HashMap k (S.HashSet v)
inserts k v m = M.insert k (S.insert v $ M.lookupDefault S.empty k m) m

removes :: (Eq k, Eq v, Hashable k, Hashable v)
        => k -> v -> M.HashMap k (S.HashSet v) -> M.HashMap k (S.HashSet v)
removes k v m = M.insert k (S.delete v (M.lookupDefault S.empty k m)) m
