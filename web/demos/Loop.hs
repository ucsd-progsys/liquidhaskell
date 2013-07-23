{--! run liquid with no-termination -}

module Loop where
import Prelude hiding ((!!), length)
import SimpleRefinements hiding (loop)

-- | Higher Order Specifications

loop :: Int -> Int -> a -> (Int -> a -> a) -> a
loop lo hi base f = go lo base
  where go i acc | i < hi    = go (i+1) (f i acc)
                 | otherwise = acc

{-@ listNatSum :: L Nat -> Nat @-}
listNatSum     :: L Int -> Int
listNatSum xs  = loop 0 n 0 body 
  where body   = \i acc -> acc + (xs !! i)
        n      = length xs

{-@ listEvenSum :: L Even -> Even @-}
listEvenSum     :: L Int -> Int
listEvenSum xs  = loop 0 n 0 body 
  where body   = \i acc -> acc + (xs !! i)
        n      = length xs

-- | Another Example

{-@ add :: n:Nat -> m:Nat -> {v:Int| v = m + n} @-}
add     :: Int -> Int -> Int
add n m = loop 0 m n (\_ i -> i + 1)
