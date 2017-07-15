{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module Fib0 where 

{-@ reflect fibExp @-}
{-@ fibExp :: Nat -> Nat @-}
fibExp :: Int -> Int
fibExp n 
  | n == 0    = 0 
  | n == 1    = 1 
  | otherwise = fibExp (n-2) + fibExp (n-1)

-- 0 => 0
-- 1 => 1 
-- 2 => 1 
-- 3 => 2 

{-@ test :: a -> { fibExp 3 == 2 } @-}  
test  :: a -> ()
test _ = ()
