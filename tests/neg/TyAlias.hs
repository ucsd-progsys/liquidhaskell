module Foo where 

{-@ measure listLength @-}
{-@ listLength :: xs:_ -> {v:Nat | v == len xs } @-}
listLength :: [a] -> Int
listLength [] = 0
listLength (_x:xs) = 1 + listLength xs

data Set a = Set [a] 
{-@ data Set a = Set [a]<{\x y -> x < y}> @-}


{-@ measure setSize @-}
{-@ setSize :: Set a -> Nat @-}
setSize :: Set a -> Int
setSize (Set xs) = listLength xs

type BinaryRelation a b = Set (a, b)
{-@ type BinaryRelationGT a b P = Set { p:(a, b) | P < p } @-}

-- | Given (a,b), for every (x,y) in the relation if b==x add (a,y) to the
-- result or if y==a add (x,b) to the result.
--
-- >>> brTransitivitySweep (1,2) (Set [(2,3)])
-- {(1,3),(2,3)}
--
-- >>> brTransitivitySweep (2,3) $ Set [(2,999)]
-- {(2,999)}
--
-- >>> brTransitivitySweep (1,2) $ Set [(2,999)]
-- {(1,999),(2,999)}
--
-- >>> brTransitivitySweep (1,2) $ Set [(2,3),(2,999)] -- BUG
-- {(1,3),(2,3),(1,999),(2,999)}
--
{-@
brTransitivitySweep
    ::  p:(a, a)
    -> br:BinaryRelationGT a a {p}
    ->    BinaryRelationGT a a {p}
    / [setSize br]
@-}
brTransitivitySweep :: Eq a => (a, a) -> BinaryRelation a a -> BinaryRelation a a
brTransitivitySweep _ (Set []) = Set []
brTransitivitySweep (a,b) (Set ((x,y):rest0))
    | b == x    = Set ((a,y):(x,y):rest1) -- a->b, x->y, b==x implies a->y | (a,b) < (x,y) && b == x  => (a,y) < (x,y)
    | y == a    = Set ((x,b):(x,y):rest1) -- x->y, a->b, y==a implies x->b
    | otherwise = Set (      (x,y):rest1)
  where
    Set rest1 = brTransitivitySweep (a,b) (Set rest0)


-- bar = brTransitivitySweep (1,2) $ Set [(2,3),(2,999)] 