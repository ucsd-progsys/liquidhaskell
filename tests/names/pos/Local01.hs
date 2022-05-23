module Local01 where

{-@ foo :: Nat @-} 
foo = incr 10 20 
  where 
    {-@ incr :: Nat -> Nat -> Nat @-}
    incr :: Int -> Int -> Int 
    incr 0 x = x + 1
    incr n x = incr (n-1) x

{-@ bar :: {v:Int | v < 0} @-} 
bar = decr 0 
  where 
    {-@ decr :: x:Int -> {v:Int | v < x} @-}
    decr :: Int -> Int 
    decr x = x - 1 


