module ListSetDemo () where

-------------------------------------------------------------------------
-- | Encoding Sets of Values With Liquid Types --------------------------
-------------------------------------------------------------------------

-- First, lets import the `Set` type from @Data.Set@

import qualified Data.Set as S 

-- Next, lets write a measure for the set of elements in a list.

{-@ measure elts @-}
elts :: (Ord a) => [a] -> S.Set a 
elts []     = S.empty
elts (x:xs) = S.union (S.singleton x) (elts xs)

-- OK, now we can write some specifications!

-- | To start with, lets check that the `elts` measure is sensible

{-@ myid :: xs:[a] -> {v:[a]| (elts v) = (elts xs)} @-}
myid []     = []
myid (x:xs) = x : myid xs

-- | The reverse function should also return the same set of values.
-- Note that the reverse uses the tail-recursive helper @go@. 
-- Mouse over and see what type is inferred for it!

{-@ decrease go 2 @-}
{-@ myrev :: xs:[a] -> {v:[a]| (elts v) = (elts xs)} @-}
myrev = go [] 
  where 
    go acc []     = acc
    go acc (y:ys) = go (y:acc) ys

-- | Next, here's good old List-append, but now with a specification about
-- the sets of values in the input and output.

{-@ myapp :: xs:[a] -> ys:[a] -> {v:[a] | (elts v) = (Set_cup (elts xs) (elts ys))} @-}
myapp []     ys = ys
myapp (x:xs) ys = x : myapp xs ys

-- | Finally, to round off this little demo, here's @filter@, which returns a subset.

{-@ myfilter :: (a -> Bool) -> xs:[a] -> {v:[a]| Set_sub (elts v) (elts xs) } @-}
myfilter f []     = []
myfilter f (x:xs) 
  | f x           = x : myfilter f xs 
  | otherwise     = myfilter f xs





