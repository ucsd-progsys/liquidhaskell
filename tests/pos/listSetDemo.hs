module ListSets () where


-------------------------------------------------------------------------
-- | Encoding Sets of Values With Liquid Types --------------------------
-------------------------------------------------------------------------

-- First, lets import the `Set` type from @Data.Set@

import Data.Set (Set (..)) 

-- Next, lets write a measure for the set of elements in a list.

{-@ measure elts :: [a] -> (Set a) 
    elts ([])   = {v | Set_emp v }
    elts (x:xs) = {v | v = Set_cup (Set_sng x) (elts xs) }
  @-}

-- Next, we tell the solver to interpret @Set@ natively in the refinement logic.

{-@ embed Set as Set_Set @-}

-- OK, now we can write some specifications!

-- | To start with, lets check that the `elts` measure is sensible

{-@ myid :: xs:[a] -> {v:[a]| (elts v) = (elts xs)} @-}
myid []     = []
myid (x:xs) = x : myid xs

-- | The reverse function should also return the same set of values.
-- Note that the reverse uses the tail-recursive helper @go@. 
-- Mouse over and see what type is inferred for it!

{-@ Decrease go 2 @-}
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





