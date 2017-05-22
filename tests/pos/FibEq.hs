{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module FibEq where 

fibInv  :: Int -> Int -> () 
fibLin  :: Int -> Int 
fibLin' :: Int -> Int -> Int -> Int 
fibExp  :: Int -> Int 
fibEq   :: Int -> () 

-- | Exponential `fib` implementation --------------------------------

{-@ reflect fibExp @-}
{-@ fibExp :: Nat -> Nat @-}
fibExp n 
  | n == 0    = 0 
  | n == 1    = 1 
  | otherwise = fibExp (n-2) + fibExp (n-1)

-- | Linear `fib` implementation ------------------------------------ 

{-@ reflect fibLin' @-}
{-@ fibLin' :: Nat -> Nat -> Nat -> Nat @-}
fibLin' n a b 
  | n == 0    = b 
  | otherwise = fibLin' (n - 1) (a + b) a

{-@ reflect fibLin @-}
{-@ fibLin :: Nat -> Nat @-}
fibLin n = fibLin' n 1 0

-- | Invariant relating the two implementations -------------------- 

{-@ fibInv :: d:Nat -> u:Nat -> 
      {fibLin' d (fibExp (1+u)) (fibExp u) = fibExp (d+u)} 
  @-}
fibInv d u 
  | d == 0    = () 
  | otherwise = fibInv (d-1) (u+1)

-- | Equivalence of two implementations ---------------------------- 

{-@ fibEq :: n:Nat -> {fibLin n = fibExp n} @-}
fibEq n = fibInv n 0 


