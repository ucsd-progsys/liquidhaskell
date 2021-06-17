
-- | Proving ackermann properties from
-- | http://www.cs.yorku.ca/~gt/papers/Ackermann-function.pdf

{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--ple" @-}


module Ackermann where

import Language.Haskell.Liquid.ProofCombinators
import Helper
import Proves ((<:))

	


-- | First ackermann definition

{-@ axiomatize ack @-}
{-@ ack :: n:Nat -> x:Nat -> Nat / [n, x] @-}
ack :: Int -> Int -> Int
ack n x     | n == 0        = x + 2
            | x == 0        = 2
            | otherwise     = ack (n-1) (ack n (x-1))

-- | Second ackermann definition

{-@ axiomatize iack @-}
{-@ iack :: Nat -> Nat -> Nat -> Nat @-}
iack :: Int -> Int -> Int -> Int
iack h n x
  = if h == 0 then x else ack n (iack (h-1) n x)

-- | Equivalence of definitions

{-@ def_eq :: n:Nat -> x:Nat -> { pf:_ | ack (n+1) x == iack x n 2 }  / [x] @-}
def_eq :: Int -> Int -> Proof
def_eq n x  | x == 0        = ()
            | otherwise     = def_eq n (x-1)


-- | Lemma 2.2

{-@ lemma2 :: n:Nat -> x:Nat -> { pf:_ | x + 1 < ack n x } / [n, x] @-}
lemma2 :: Int -> Int -> Proof
lemma2 n x  | x == 0        = ()
            | n == 0        = ()
            | otherwise     =   lemma2 (n-1) (ack n (x-1))
                              ? lemma2 n     (x-1)


-- | Lemma 2.3

-- Lemma 2.3  -- NV HERE HERE 
{-@ lemma3 :: n:Nat -> x:Nat -> { pf:_ | ack n x < ack n (x+1) } @-}
lemma3 :: Int -> Int -> Proof
lemma3 n x  | x == 0        = ack n 0 <: ack n 1       ? lemma2 n 1 *** QED
            | n == 0        = ack n x <: ack n (x + 1) *** QED
            | otherwise     = lemma2 (n-1) (ack n x)

{-@ lemma3_gen :: n:Nat -> x:Nat -> y:{Nat | x < y} -> { pf:_ | ack n x < ack n y} / [y] @-}
lemma3_gen :: Int -> Int -> Int -> Proof
lemma3_gen n x y
    = gen_increasing (ack n) (lemma3 n) x y

{-@ lemma3_eq :: n:Nat -> x:Nat -> y:{Nat | x <= y} -> { pf:_ | ack n x <= ack n y} / [y] @-}
lemma3_eq :: Int -> Int -> Int -> Proof
lemma3_eq n x y | x == y    = ()
                | otherwise = lemma3_gen n x y


-- | Lemma 2.4
{-@ type Pos = {v:Int | 0 < v } @-}

{-@ lemma4 :: x:Pos -> n:Nat -> { pf:_ | ack n x < ack (n+1) x } @-}
lemma4 :: Int -> Int -> Proof
lemma4 x n  =   lemma2 (n+1) (x-1)
              ? lemma3_gen n x (ack (n+1) (x-1))

{-@ lemma4_gen :: n:Nat -> m:{Nat | n < m }-> x:Pos -> { pf:_ | ack n x < ack m x } @-}
lemma4_gen     :: Int -> Int -> Int -> Proof
lemma4_gen n m x
  = gen_increasing2 ack lemma4 x n m

{-@ lemma4_eq :: n:Nat -> x:Nat -> { pf:_ | ack n x <= ack (n+1) x } @-}
lemma4_eq     :: Int -> Int -> Proof
lemma4_eq n x   | x == 0      = ()
                | otherwise   = lemma4 x n

-- | Lemma 2.5

{-@ lemma5 :: h:Nat -> n:Nat -> x:Nat
           -> { pf:_ | iack h n x < iack (h+1) n x } @-}
lemma5 :: Int -> Int -> Int -> Proof
lemma5 h n x
  = lemma2 n (iack h n x)


-- | Lemma 2.6
{-@ lemma6 :: h:Nat -> n:Nat -> x:Nat
           -> { pf:_ | iack h n x < iack h n (x+1) } @-}
lemma6 :: Int -> Int -> Int -> Proof
lemma6 h n x  | h == 0      =  ()
              | h > 0       =   lemma6 (h-1) n x
                              ? lemma3_gen n (iack (h-1) n x) (iack (h-1) n (x+1))

{-@ lemma6_gen :: h:Nat -> n:Nat -> x:Nat -> y:{Nat | x < y}
           -> { pf:_ | iack h n x < iack h n y } /[y] @-}
lemma6_gen :: Int -> Int -> Int -> Int -> Proof
lemma6_gen h n x y
  = gen_increasing (iack h n) (lemma6 h n) x y


-- Lemma 2.7

{-@ lemma7 :: h:Nat -> n:Nat -> x:Nat
           -> { pf:_ | iack h n x <= iack h (n+1) x } @-}
lemma7 :: Int -> Int -> Int -> Proof
lemma7 h n x  | h == 0      =   () 
              | h > 0       =   lemma4_eq n (iack (h-1) n x)
                              ? lemma7 (h-1) n x
                              ? lemma3_eq (n+1) (iack (h-1) n x) (iack (h-1) (n+1) x)


-- | Lemma 9

{-@ lemma9 :: n:Pos -> x:Nat -> { l:Int | l < x + 2 }
           -> { pf:_ | x + l < ack n x } @-}
lemma9 :: Int -> Int -> Int -> Proof
lemma9 n x l  | x == 0      =   ack n 0 === 2 *** QED
              | n == 1      =   lemma9_helper x l -- *** QED
              | otherwise   =   lemma4_gen 1 n x
                              ? lemma9_helper x l


{-@ lemma9_helper  :: x:Nat -> { l:Int | l < x + 2 }
            -> { pf:_ | x + l < ack 1 x } @-}
lemma9_helper :: Int -> Int -> Proof
lemma9_helper x l  | x == 0   = ack 1 0 === 2 *** QED
                   | x > 0    = lemma9_helper (x-1) (l-1)   -- FAIL with interpreter
----                              ? toProof ( ack 1 x === ack 0 (ack 1 (x-1)) )

-- | Lemma 2.10

{-@ lemma10 :: n:Nat -> x:Pos -> { l:Nat | 2 * l < x}
            -> { pf:_ | iack l n x < ack (n+1) x } @-}
lemma10 :: Int -> Int -> Int -> Proof
lemma10 n x l   | n == 0        =   lemma10_zero l x
                                  ? lemma10_one x
                | l == 0        =   lemma2 (n+1) x
                | otherwise     =   def_eq n x
                                  ? ladder_prop1 n x 2
                                  ? ladder_prop2 l (x-l) n 2
                                  ? lemma10_helper n x l
                                  ? ladder_prop1 n (x-l) 2
                                  ? ladder_prop3 x (ladder (x-l) n 2) n l
                                  ? ladder_prop1 n l x


{-@ lemma10_zero :: l:Nat -> x:Nat -> { pf:_ | iack l 0 x == x + 2 * l } @-}
lemma10_zero :: Int -> Int -> Proof
lemma10_zero l x    | l == 0    = iack 0 0 x === x *** QED
                    | l > 0     = lemma10_zero (l-1) x        -- FAIL
----                                ? toProof ( iack l 0 x === ack 0 (iack (l-1) 0 x) )
{-@ lemma10_one :: x:Nat -> { pf:_ | ack 1 x == 2 + 2 * x} @-}
lemma10_one :: Int -> Proof
lemma10_one x   | x == 0        = ack 1 0 === 2 *** QED
                | otherwise     = lemma10_one (x-1)           -- FAIL
----                                ? toProof ( ack 1 x === ack 0 (ack 1 (x-1)) )

{-@ lemma10_helper :: n:Nat -> x:{Int | 0 < x } -> l:{Nat | 2 * l < x && x-l >=0}
            -> { pf:_ |  x < iack (x-l) n 2 } @-}
lemma10_helper :: Int -> Int -> Int -> Proof
lemma10_helper n x l            =   def_eq n (x-l)
                                  ? lemma9 (n+1) (x-l) l


-- | Lader as helper definition and properties
{-@ axiomatize ladder @-}
{-@ ladder :: Nat -> {n:Int | 0 < n } -> Nat -> Nat @-}
ladder :: Int -> Int -> Int -> Int
ladder l n b    | l == 0        = b
                | otherwise     = iack (ladder (l-1) n b) (n-1) 2


{-@ ladder_prop1 :: n:{Int | 0 < n} -> l:Nat -> x:Nat
                 -> { pf:_ | iack l n x == ladder l n x} / [l] @-} 
ladder_prop1 :: Int -> Int -> Int -> Proof
ladder_prop1 n l x  | l == 0        =   iack 0 n x === ladder 0 n x *** QED
                    | otherwise     =   ladder_prop1 n (l-1) x
                                      ? def_eq (n-1) (ladder (l-1) n x)


{-@ ladder_prop2 :: x:Nat -> y:Nat -> n:{Int | 0 < n} -> z:Nat
                 -> { pf:_ | ladder (x + y) n z == ladder x n (ladder y n z)} / [x] @-}
ladder_prop2 :: Int -> Int -> Int -> Int -> Proof
ladder_prop2 x y n z  | x == 0      = ladder 0 n (ladder y n z) === ladder y n z *** QED
                      | otherwise   = ladder_prop2 (x-1) y n z

{-@ ladder_prop3 :: x:Nat -> y:{Nat | x < y} -> n:{Int | 0 < n} -> l:Nat
                 -> { pf:_ | ladder l n x < ladder l n y }  @-}
ladder_prop3 :: Int -> Int -> Int -> Int -> Proof
ladder_prop3 x y n l    =   ladder_prop1 n l x
                          ? ladder_prop1 n l y
                          ? lemma6_gen l n x y

-- | Lemma 2.11

{-@ lemma11 :: n:Nat -> x:Nat -> y:Nat -> { pf:_ | iack x n y < ack (n+1) (x+y) } @-}
lemma11 :: Int -> Int -> Int -> Proof
lemma11 n x y   =   def_eq n (x+y)
                  ? lemma11_helper n x y 2
                  ? def_eq n y
                  ? lemma2 (n+1) y
                  ? lemma6_gen x n y (ack (n+1) y)

{-@ lemma11_helper :: n:Nat -> x:Nat -> y:Nat -> z:Nat
             -> { pf:_ | iack (x+y) n z == iack x n (iack y n z) } / [x] @-}
lemma11_helper :: Int -> Int -> Int -> Int -> Proof
lemma11_helper n x y z  | x == 0  = iack y n z === iack 0 n (iack y n z) *** QED
                        | x > 0   = lemma11_helper n (x-1) y z
