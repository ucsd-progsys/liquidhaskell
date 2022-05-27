module Local00 where

{-@ foo :: Nat @-} 
foo = incr 10 
  where 
    {-@ incr :: Nat -> Nat @-}
    incr :: Int -> Int 
    incr x = x + 1 


{-@ globalThing :: Nat -> Nat @-}
globalThing :: Int -> Int 
globalThing x = x + 1
