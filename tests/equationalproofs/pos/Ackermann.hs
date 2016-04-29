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
{-@ LIQUID "--maxparams=5"     @-}
{-@ LIQUID "--eliminate"       @-}


module Ackermann where




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

-- Lemma 10 


lemma10 :: Int -> Int -> Int -> Bool
{-@ lemma10 :: n:Nat -> x:{Int | 0 < x } -> l:{Nat | 2 * l < x} 
            -> {v:Bool | iack l n x < ack (n+1) x } @-}
lemma10 n x l 
  | n == 0 
  = iack l 0 x == x + 2 * (l + 1) `with`
    lemma10' l x `with` 
    ack 1 x == 2 + 2 * x `with`
    lemma10'' x 
  | l == 0 
  = iack 0 n x == x `with`
    lemma2 (n+1) x
  | otherwise
  = ack (n+1) x == iack x n 2     `with` def_eq n x
                                  `with` iack x n 2 == ladder x n 2 `with` ladder_prop1 n x 2 
                                  `with`
    ack (n+1) x == ladder x n 2   `with` ladder x n 2 == ladder ((x-l) + l) n 2 
                                  `with`
    ack (n+1) x == ladder ((x-l) + l) n 2 
                                  `with` ladder (l + (x-l)) n 2 == ladder l n (ladder (x-l) n 2)
                                  `with` ladder_prop2 l (x-l) n 2 
                                  `with`
    ack (n+1) x == ladder l n (ladder (x-l) n 2) 
                                  `with` lemma10_helper n x l  
                                  `with` x < iack (x-l) n 2

                                  `with` iack (x-l) n 2 == ladder (x-l) n 2
                                  `with` ladder_prop1 n (x-l) 2

                                  `with` x < ladder (x-l) n 2

                                  `with` ladder_prop3 x (ladder (x-l) n 2) n l 
                                  `with` ladder l n x < ladder l n (ladder (x-l) n 2)
                                  `with`
    ack (n+1) x >  ladder l n x   `with` ladder_prop1 n l x 
                                  `with` ladder l n x == iack l n x 
                                  `with` 
    ack (n+1) x > iack l n x   



{-@ lemma10' :: l:Nat -> x:Nat -> {v:Bool | iack l 0 x == x + 2 * l } @-}
lemma10' :: Int -> Int -> Bool 
lemma10' l x 
  | l == 0 
  = iack 0 0 x == x 
  | l > 0 
  = iack l 0 x == ack 0 (iack (l-1) 0 x) `with`
    ack 0 (iack (l-1) 0 x) == (iack (l-1) 0 x) + 2 `with`
    iack (l-1) 0 x == x + 2 * (l-1) `with`
    lemma10' (l-1) x `with`
    ack 0 (iack (l-1) 0 x) == x + 2 * (l-1) + 2  



{-@ lemma10'' :: x:Nat -> {v:Bool | ack 1 x == 2 + 2 * x} @-}
lemma10'' :: Int -> Bool 
lemma10'' x
  | x == 0 
  = ack 1 0 == 2 
  | otherwise
  = ack 1 x == ack 0 (ack 1 (x-1)) `with`
    ack 0 (ack 1 (x-1)) == 2 + (ack 1 (x-1)) `with` 
    lemma10'' (x-1) `with`
    ack 1 (x-1) == 2 + 2 * (x-1) `with`
    ack 1 x == 2 + 2 * x



lemma10_helper :: Int -> Int -> Int -> Bool
{-@ lemma10_helper :: n:Nat -> x:{Int | 0 < x } -> l:{Nat | 2 * l < x && x-l >=0} 
            -> {v:Bool | x < iack (x-l) n 2 } @-}
lemma10_helper n x l 
  = iack (x-l) n 2 == ack (n+1) (x-l) `with` def_eq n (x-l) `with` 
    iack (x-l) n 2 > x `with` lemma9 (n+1) (x-l) l 

{-@ measure ladder :: Int -> Int -> Int -> Int @-}
{-@ assume ladder :: l:Nat -> n:{Int | 0 < n } -> b:Nat 
    -> {v:Nat | v == ladder l n b && (if l == 0 then (v == b) else ( v == iack (ladder (l-1) n b) (n-1) 2)) } @-} 
{-@ ladder :: Nat -> {n:Int | 0 < n } -> Nat -> Nat @-} 
ladder :: Int -> Int -> Int -> Int 
ladder l n b 
  | l == 0 
  = b 
  | otherwise
  = iack (ladder (l-1) n b) (n-1) 2



{-@ ladder_prop3 :: x:Nat -> y:{Nat | x < y} -> n:{Int | 0 < n} -> l:Nat 
   -> {v:Bool | ladder l n x < ladder l n y }  @-}
ladder_prop3 :: Int -> Int -> Int -> Int -> Bool 
ladder_prop3 x y n l
  = ladder l n x == iack l n x `with` 
    ladder_prop1 n l x `with` 
    ladder l n y == iack l n y `with`
    ladder_prop1 n l y `with`
    iack l n x < iack l n y `with`
    lemma6' l n x y 


{-@ ladder_prop2 :: x:Nat -> y:Nat -> n:{Int | 0 < n} -> z:Nat 
   -> {v:Bool | ladder (x + y) n z == ladder x n (ladder y n z)} / [x] @-}
ladder_prop2 :: Int -> Int -> Int -> Int -> Bool 
ladder_prop2 x y n z 
  | x == 0 
  = ladder 0 n (ladder y n z) == ladder y n z 
  | otherwise
  = ladder_prop2 (x-1) y n z `with`
    ladder (x+y) n z == iack (ladder (x+y-1) n z) (n-1) 2 `with`
    ladder (x+y) n z == iack (ladder (x-1) n (ladder y n z)) (n-1) 2 `with`
    ladder (x+y) n z == ladder x n (ladder y n z)


{-@ ladder_prop1 :: n:{Int | 0 < n} -> l:Nat -> x:Nat -> {v:Bool | iack l n x == ladder l n x} / [l] @-}
ladder_prop1 :: Int -> Int -> Int -> Bool 
ladder_prop1 n l x 
  | l == 0 
  = iack 0 n x == x `with` 
    ladder 0 n x == x  
  | otherwise
  = iack l n x == ack n (iack (l-1) n x) `with`
    ladder_prop1 n (l-1) x `with` 
    iack (l-1) n x == ladder (l-1) n x `with` 
    iack l n x == ack n (ladder (l-1) n x) `with`
    def_eq (n-1) (ladder (l-1) n x) `with`
    ack n (ladder (l-1) n x) == iack (ladder (l-1) n x) (n-1) x `with`
    iack l n x == ladder l n x  





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


lemma3_gen :: Int -> Int -> Int -> Bool
{-@ lemma3_gen :: n:Nat -> x:Nat -> y:{v:Nat | x < v} -> {v:Bool | ack n x < ack n y} / [y] @-}
lemma3_gen n x y
    = gen_increasing (ack n) (lemma3 n) x y
