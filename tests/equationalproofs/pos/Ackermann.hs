{-
Proving ackermann properties from http://www.cs.yorku.ca/~gt/papers/Ackermann-function.pdf
-}


{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE ExtendedDefaultRules #-}
{-# LANGUAGE FlexibleContexts     #-}
{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--autoproofs"      @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--no-prune"        @-}
{-@ LIQUID "--maxparams=5"     @-}


module FunctionAbstraction where




{-
TODO
  - allow terminating expressions for assumed
  - allow preconditions in assumed 
  - provide assumed types for ack with axiomatization
-}

{-@ measure ack :: Int -> Int -> Int @-}
-- assumed specs cannot have termination expressions 


{-@ assume ack :: n:Nat -> x:Nat
      -> {v:Nat| v == ack n x && if n == 0 then v == x + 2 else (if x == 0 then v == 2 else v == (ack (n-1) (ack n (x-1))))}@-}

{-@ ack :: n:Nat -> x:Nat -> Nat / [n, x] @-}
ack :: Int -> Int -> Int 
ack n x 
  | n == 0
  = x + 2
  | x == 0 
  = 2 
  | n > 0, x > 0 
  = ack (n-1) (ack n (x-1))


{-@ Lazy iack @-}
{-@ measure iack :: Int -> Int -> Int -> Int @-}
{-@ iack :: Nat -> Nat -> Nat -> Int @-}
{-@ assume iack :: h:Nat -> n:Nat -> x:Nat 
                -> {v:Nat | v == iack h n x && if h == 0 then (v == x) else (v == ack n (iack (h-1) n x) )} @-}
iack :: Int -> Int -> Int -> Int 
iack h n x = if h == 0 then x else ack n (iack (h-1) n x)


-- Equivalence of definitions

def_eq :: Int -> Int -> Bool 
{-@ def_eq :: n:Nat -> x:Nat ->{v: Bool | ack (n+1) x == iack x n 2 } / [x]@-} 
def_eq n x 
  | x == 0 
  = ack (n+1) 0 == 2 `with`
    iack 0 n 2 == 2 
  | otherwise
  = ack (n+1) x == ack n (ack (n+1) (x-1)) `with` 
    def_eq n (x-1) `with`
    ack (n+1) (x-1) == iack (x-1) n 2 `with`
    ack (n+1) x == iack x n 2 



-- Lemma 2.2

lemma2 :: Int -> Int -> Bool 
{-@ lemma2 :: n:Nat -> x:Nat -> {v:Bool | x + 1 < ack n x } / [n, x] @-}
lemma2 n x 
  | x == 0 
  = ack n 0 == 2
  | n == 0 
  = ack 0 x == x + 1  
  | otherwise
  = ack n x  == ack (n-1) (ack n (x-1)) `with` 
    lemma2 (n-1) (ack n (x-1))          `with`
    (ack n (x-1)) + 1 < ack n x         `with`
    lemma2 n (x-1)                      `with`
    x < ack n (x-1)   

-- Lemma 2.3 
lemma3 :: Int -> Int -> Bool 
{-@ lemma3 :: n:Nat -> x:Nat -> {v:Bool | ack n x < ack n (x+1)} @-}
lemma3 n x 
  | x == 0 
  = ack n 0 < ack n 1 `with` 
    ack n 0 == 2      `with` 
    lemma2 n 1        `with`
    2 < ack n 1 
  | n == 0 
  = ack n x < ack n (x + 1)
  | otherwise
  = ack n (x+1)  == ack (n-1) (ack n x) `with`
    lemma2 (n-1) (ack n x)              `with`
    ack n x < ack n (x+1) 


lemma3' :: Int -> Int -> Int -> Bool 
{-@ lemma3' :: n:Nat -> x:Nat -> y:{v:Nat | x < v} -> {v:Bool | ack n x < ack n y} / [y] @-}
lemma3' n x y 
  | x + 1 < y 
  = lemma3' n x (y-1)      `proves`
     ack n x < ack n (y-1)  `with` 
     lemma3 n (y-1)        `proves`
     ack n x < ack n y 


  | x + 1 == y 
  = lemma3 n x `with` 
     ack n x < ack n y 
     
  | otherwise
  = True


lemma3'' :: Int -> Int -> Int -> Bool 
{-@ lemma3'' :: n:Nat -> x:Nat -> y:{v:Nat | x <= v} -> {v:Bool | ack n x <= ack n y} / [y] @-}
lemma3'' n x y 
  | x == y 
  = ack n x == ack n y 
  | otherwise
  = lemma3' n x y 


-- Lemma 2.4 

lemma4 :: Int -> Int -> Bool 
{-@ lemma4 :: n:Nat -> x:{Int | x > 0 } -> {v:Bool | ack n x < ack (n+1) x } @-}
lemma4 n x
  = lemma2 (n+1) (x-1) `proves` 
      x < ack (n+1) (x-1) `with`
    lemma3' n x (ack (n+1) (x-1)) `proves`
      ack n x < ack n (ack (n+1) (x-1)) `with`
      ack (n+1) x == ack n (ack (n+1) (x-1)) `with`
      ack n x < ack (n+1) x 


lemma4' :: Int -> Int -> Bool 
{-@ lemma4' :: n:Nat -> x:Nat -> {v:Bool | ack n x <= ack (n+1) x } @-}
lemma4' n x
  | x == 0 
  = ack n x     == 2 `with`
    ack (n+1) x == 2  
  | otherwise
  = lemma4 n x 


lemma4'' :: Int -> Int -> Int -> Bool 
{-@ lemma4'' :: n:Nat -> m:{Nat | m < n}-> x:{Int | x > 0 } -> {v:Bool | ack m x < ack n x } @-}
lemma4'' n m x
  | n == m + 1 
  =  lemma4 m x  `with` 
     ack m x < ack n x 
  | otherwise
  = lemma4'' (n-1) m  x `with`
    ack m x < ack (n-1) x `with`
    lemma4' (n-1) x `with`
    ack (n-1) x < ack n x 
-- Lemma 2.5 

lemma5 :: Int -> Int -> Int -> Bool 
{-@ lemma5 :: h:Nat -> n:Nat -> x:Nat
           -> {v:Bool | iack h n x < iack (h+1) n x } @-}
lemma5 h n x
  = lemma2 n (iack h n x) `proves`
    iack h n x < ack n (iack h n x) `with`
    iack (h+1) n x == ack n (iack h n x)


-- Lemma 2.6 
lemma6 :: Int -> Int -> Int -> Bool 
{-@ lemma6 :: h:Nat -> n:Nat -> x:Nat
           -> {v:Bool | iack h n x < iack h n (x+1) } @-}

lemma6 h n x
  | h == 0 
  = iack h n x == x `with`
    x < x + 1 `with`
    iack h n (x+1) == x + 1 
  | h > 0 
  = lemma6 (h-1) n x `with` 
    iack (h-1) n x < iack (h-1) n (x+1) `with` 
    lemma3' n (iack (h-1) n x) (iack (h-1) n (x+1)) `with`
    ack n (iack (h-1) n x) < ack n (iack (h-1) n (x+1)) `with`
    ack n (iack (h-1) n x) == iack h n x `with`
    ack n (iack (h-1) n (x+1)) == iack h n (x+1) `with`
    iack h n x < iack h n (x+1) `with` 
    iack h n x < iack h n (x+1)

lemma6' :: Int -> Int -> Int -> Int -> Bool 
{-@ lemma6' :: h:Nat -> n:Nat -> x:Nat -> y:{Nat | x < y}
           -> {v:Bool | iack h n x < iack h n y } /[y] @-}
lemma6' h n x y 
  | y == x + 1 
  = lemma6 h n x `with`
    iack h n x < iack h n y 
  | otherwise
  = lemma6' h n x (y-1) `with`
    iack h n x < iack h n (y-1) `with`
    lemma6 h n (y-1) `with`
    iack h n (y-1) < iack h n y 



lemma7 :: Int -> Int -> Int -> Bool 
{-@ lemma7 :: h:Nat -> n:Nat -> x:Nat
           -> {v:Bool | iack h n x <= iack h (n+1) x } @-}
lemma7 h n x 
  | x == 0 , h == 0 
  = iack 0 n 0 == ack n 0 `with` 
    ack n 0 == 2 `with`
    iack 0 (n+1) 0 == ack (n+1) 0 `with` 
    ack (n+2) 0 == 2 

  | h == 0
  = iack 0 n x == ack n x `with` 
    iack 0 (n+1) x == ack (n+1) x `with` 
    lemma4 n x 

  | h > 0 
  = iack h n x == ack n (iack (h-1) n x) `with` 
    lemma4' n (iack (h-1) n x) `with` 
    ack n (iack (h-1) n x) <= ack (n+1) (iack (h-1) n x) `with`
    lemma7 (h-1) n x `with`
    iack (h-1) n x <= iack (h-1) (n+1) x `with` 
    lemma3'' (n+1) (iack (h-1) n x) (iack (h-1) (n+1) x) `with` 
    ack (n+1) (iack (h-1) n x) <= ack (n+1) (iack (h-1) (n+1) x) `with`
    ack (n+1) (iack (h-1) (n+1) x) == iack h (n+1) x 


{-  desired proof 
       iack h n x 
     === ack n (iack (h-1) n x) {- lemma4: ack n x < ack (n+1) x-}
       < ack (n+1) (iack (h-1) n x) 
       {- IH iack (h-1) n c <= iack (h-1) (n+1) x -}
       {- lemma3' ack (n+1) (iack (h-1) n c) <= ack (n+1) (iack (h-1) (n+1) x) -}
       <= ack (n+1) (iack (h-1) (n+1) x)
     === iack h (n+1) x 
-}

-- Lemma 9

lemma9 :: Int -> Int -> Int -> Bool 
{-@ lemma9 :: n:{Int | n > 0} -> x:Nat -> l:{Int | l < x + 2 } 
            -> {v:Bool | x + l < ack n x } @-}
lemma9 n x l 
  | x == 0 
  = ack n 0 == 2 
  | n == 1 
  = lemma90 x l `with` x+1 < ack 1 x 
  | otherwise 
  = ack 1 x < ack n x `with`
    lemma4'' n 1 x `with` 
    ack 1 x > x + l `with`
    lemma90 x l  



lemma90 :: Int -> Int -> Bool 
{-@ lemma90 :: x:Nat -> l:{Int | l < x + 2 } 
            -> {v:Bool | x + l < ack 1 x } @-}
lemma90 x l
  | x == 0
  = ack 1 0 == 2
  | x > 0 
  = ack 1 x == ack 0 (ack 1 (x-1)) `with` 
    ack 0 (ack 1 (x-1)) == ack 1 (x-1) + 2 `with` 
    lemma90 (x-1) (l-1) `with` 
    ack 1 (x-1) > x + l `with` 
    ack 1 x > x + l   

-- Lemma 11 

lemma11 :: Int -> Int -> Int -> Bool 
{-@ lemma11 :: n:Nat -> x:Nat -> y:Nat -> {v:Bool | iack x n y < ack (n+1) (x+y) } @-}
lemma11 n x y
  = ack (n+1) (x+y) == iack (x+y) n 2 `with`
    def_eq n (x+y) `with`
    iack (x+y) n 2 == iack x n (iack y n 2) `with` 
    lemma11' n x y 2 `with`
    iack y n 2 == ack (n+1) y `with`
    def_eq n y `with`
    lemma2 (n+1) y `with`
    y < ack (n+1) y `with`
    -- I was here 
    ack (n+1) (x+y) == iack x n (ack (n+1) y) `with` 
    -- I want 
    iack x n (ack (n+1) y) > iack x n y  `with` 
    lemma6' x n y (ack (n+1) y)



lemma11' :: Int -> Int -> Int -> Int -> Bool 
{-@ lemma11' :: n:Nat -> x:Nat -> y:Nat -> z:Nat 
             -> {v:Bool | iack (x+y) n z == iack x n (iack y n z) } / [x] @-}
lemma11' n x y z
  | x == 0 
  = iack y n z == iack 0 n (iack y n z) 
  | x>0
  = lemma11' n (x-1) y z `with`
    iack ((x-1)+y) n z == iack (x-1) n (iack y n z) `with` 
    iack (x+y) n z == ack n (iack (x+y-1) n z) `with`
    ack n (iack (x-1) n (iack y n z)) == iack x n (iack y n z)




infixr 2 `with`
infixr 2 `proves`


{-@ with, proves  :: p:Bool -> q:Bool -> {v:Bool | Prop v <=> Prop p && Prop q } @-}
proves, with :: Bool -> Bool -> Bool
with   p q = p && q 
proves p q = p && q 


data Proof = Proof 


