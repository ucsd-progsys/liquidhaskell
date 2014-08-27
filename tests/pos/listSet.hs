module ListSets () where

-------------------------------------------------------------------------
-- | Encoding Sets of Values With Liquid Types --------------------------
-------------------------------------------------------------------------

-- TODO: make this self-enclosed

import Data.Set (Set(..))  

-- | To start with, lets check that the `listElts` measure is sensible

{-@ myid0 :: xs:[a] -> {v:[a]| (len v) = (len xs)} @-}
myid0 []     = []
myid0 (x:xs) = x : myid0 xs


{-@ myid :: xs:[a] -> {v:[a]| (listElts v) = (listElts xs)} @-}
myid []     = []
myid (x:xs) = x : myid xs

-- | The reverse function should also return the same set of values.
-- Note that the reverse uses the tail-recursive helper @go@. 
-- Mouse over and see what type is inferred for it!

{-@ Decrease go 2 @-}
{-@ myrev :: xs:[a] -> {v:[a]| listElts(v) = listElts(xs)} @-}
myrev :: [a] -> [a]
myrev = go [] 
  where 
    go acc []     = acc
    go acc (y:ys) = go (y:acc) ys

-- | Next, here's good old List-append, but now with a specification about
-- the sets of values in the input and output.

{-@ myapp :: xs:[a] 
          -> ys:[a] 
          -> {v:[a] | listElts v = Set_cup (listElts xs) (listElts ys) } @-}
myapp :: [a] -> [a] -> [a]
myapp []     ys = ys
myapp (x:xs) ys = x : myapp xs ys

-- | Finally, to round off this little demo, here's @filter@, which returns a subset.

{-@ myfilter :: (a -> Bool) -> xs:[a] -> {v:[a] | Set_sub (listElts v) (listElts xs) } @-}
myfilter :: (a -> Bool) -> [a] -> [a]
myfilter f []     = []
myfilter f (x:xs) = if f x 
                      then x : myfilter f xs 
                      else myfilter f xs





