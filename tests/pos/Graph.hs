module Graph where

import Data.Set


type Size = Int
data Map k v = Tip | Bin Size k v (Map k v) (Map k v)
             deriving (Eq, Ord)


data Edges edge 


{-@ measure getEdgesIncoming :: (Edges edge) -> (Set edge) @-}

{-@ measure getEdgesOutgoing :: (Edges edge) -> (Set edge) @-}

data Graph node edge = 
  Graph {
    graphMap :: 
      Map node (Edges edge, Edges edge)
  }


{-@ invariant {v: (Graph node edge) | (getGraphIncoming v) = (getGraphOutgoing v) } @-}

{-@ measure getGraphIncoming :: (Graph node edge) -> (Set edge)
    getGraphIncoming (Graph m) = (getMapIncoming m)
  @-}

{-@ measure getGraphOutgoing :: (Graph node edge) -> (Set edge)
    getGraphOutgoing (Graph m) = (getMapOutgoing m)
  @-}


{-@ measure getMapIncoming :: (Map node (Edges edge, Edges e)) -> (Set edge)
    getMapIncoming (Tip) = {v | (? (Set_emp v))}
    getMapIncoming (Bin size k v lm rm) = (Set_cup (getPairIncoming v) (Set_cup (getMapIncoming lm) (getMapIncoming rm)))
  @-}


{-@ measure getMapOutgoing :: (Map node (Edges edge, Edges edge)) -> (Set edge)
    getMapOutgoing (Tip) = {v | (? (Set_emp v))}
    getMapOutgoing (Bin size k v lm rm) = (Set_cup (getPairOutgoing v) (Set_cup (getMapOutgoing lm) (getMapOutgoing rm)))
  @-}

{-@ measure getPairIncoming :: (Edges edge, Edges e) -> (Set edge)
    getPairIncoming (x, y) = (getEdgesIncoming x)
  @-}

{-@ measure getPairOutgoing :: (Edges edge, Edges e) -> (Set edge)
    getPairOutgoing (x, y) = (getEdgesOutgoing y)
  @-}

