
-- | Proving ackermann properties from
-- | http://www.cs.yorku.ca/~gt/papers/Ackermann-function.pdf

{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--autoproofs"      @-}
{-@ LIQUID "--totality"        @-}


module Ackermann where

import Proves
import Helper

-- | First ackermann definition

{-@ axiomatize ack @-}
{-@ ack :: n:Nat -> x:Nat -> Nat / [n, x] @-}
ack :: Int -> Int -> Int
ack n x
  | n == 0
  = x + 2
  | x == 0
  = 2
  | otherwise
  = ack (n-1) (ack n (x-1))

-- | Second ackermann definition

{-@ axiomatize iack @-}
{-@ iack :: Nat -> Nat -> Nat -> Nat @-}

iack :: Int -> Int -> Int -> Int
iack h n x
  = if h == 0 then x else ack n (iack (h-1) n x)

-- | Equivalence of definitions

{-@ def_eq :: n:Nat -> x:Nat -> { ack (n+1) x == iack x n 2 }  / [x] @-}
def_eq :: Int -> Int -> Proof
def_eq n x
  | x == 0
  =   ack (n+1) 0
  ==. 2
  ==. iack 0 n 2
  *** QED

  | otherwise
  =   ack (n+1) x
  ==. ack n (ack (n+1) (x-1))
  ==. ack n (iack (x-1) n 2)   ? def_eq n (x-1)
  ==. iack x n 2
  *** QED


-- | Lemma 2.2

lemma2 :: Int -> Int -> Proof
{-@ lemma2 :: n:Nat -> x:Nat -> { x + 1 < ack n x } / [n, x] @-}
lemma2 n x
  | x == 0
  = ack n 0 ==. 2 *** QED
  | n == 0
  = ack 0 x ==. x + 2 *** QED
  | otherwise
  =   ack n x
  ==. ack (n-1) (ack n (x-1))
   >. ack n (x-1)              ? lemma2 (n-1) (ack n (x-1))
   >. x                        ? lemma2 n (x-1)
  *** QED


-- | Lemma 2.3

-- Lemma 2.3
lemma3 :: Int -> Int -> Proof
{-@ lemma3 :: n:Nat -> x:Nat -> { ack n x < ack n (x+1) } @-}
lemma3 n x
  | x == 0
  = ack n 0 <. ack n 1 ? lemma2 n 1 *** QED
  | n == 0
  = ack n x <. ack n (x + 1) *** QED
  | otherwise
  =   ack n x
  <.  ack (n-1) (ack n x) ? lemma2 (n-1) (ack n x)
  <.  ack n (x+1)
  *** QED

lemma3_gen :: Int -> Int -> Int -> Proof
{-@ lemma3_gen :: n:Nat -> x:Nat -> y:{Nat | x < y} -> {ack n x < ack n y} / [y] @-}
lemma3_gen n x y
    = gen_increasing (ack n) (lemma3 n) x y

lemma3_eq :: Int -> Int -> Int -> Proof
{-@ lemma3_eq :: n:Nat -> x:Nat -> y:{Nat | x <= y} -> {ack n x <= ack n y} / [y] @-}
lemma3_eq n x y
  | x == y
  = ack n x ==. ack n y *** QED
  | otherwise
  = lemma3_gen n x y


-- | Lemma 2.4
{-@ type Pos = {v:Int | 0 < v } @-}

lemma4 :: Int -> Int -> Proof
{-@ lemma4 :: x:Pos -> n:Nat -> { ack n x < ack (n+1) x } @-}
lemma4 x n
  =   ack (n+1) x
  ==. ack n (ack (n+1) (x-1))
   >. ack n x                   ?  lemma2 (n+1) (x-1)
                               ==> lemma3_gen n x (ack (n+1) (x-1))
  *** QED

lemma4_gen     :: Int -> Int -> Int -> Proof
{-@ lemma4_gen :: n:Nat -> m:{Nat | n < m }-> x:Pos -> { ack n x < ack m x } @-}
lemma4_gen n m x
  = gen_increasing2 ack lemma4 x n m


lemma4_eq     :: Int -> Int -> Proof
{-@ lemma4_eq :: n:Nat -> x:Nat -> { ack n x <= ack (n+1) x } @-}
lemma4_eq n x
  | x == 0
  = ack n x ==. ack (n+1) x *** QED
  | otherwise
  = lemma4 x n


-- | Lemma 2.5

lemma5 :: Int -> Int -> Int -> Proof
{-@ lemma5 :: h:Nat -> n:Nat -> x:Nat
           -> {iack h n x < iack (h+1) n x } @-}
lemma5 h n x
  =  iack h n x
  <. ack n (iack h n x) ? lemma2 n (iack h n x)
  <. iack (h+1) n x
  *** QED


-- | Lemma 2.6
lemma6 :: Int -> Int -> Int -> Proof
{-@ lemma6 :: h:Nat -> n:Nat -> x:Nat
           -> { iack h n x < iack h n (x+1) } @-}

lemma6 h n x
  | h == 0
  =   iack h n x
  ==. x
   <. x + 1
   <. iack h n (x+1)
  *** QED
  | h > 0
  =   iack h n x
  ==. ack n (iack (h-1) n x) ? (  lemma6 (h-1) n x
                              ==> lemma3_gen n (iack (h-1) n x) (iack (h-1) n (x+1))
                               )
   <. ack n (iack (h-1) n (x+1))
   <. iack h n (x+1)
  *** QED


lemma6_gen :: Int -> Int -> Int -> Int -> Proof
{-@ lemma6_gen :: h:Nat -> n:Nat -> x:Nat -> y:{Nat | x < y}
           -> { iack h n x < iack h n y } /[y] @-}
lemma6_gen h n x y
  = gen_increasing (iack h n) (lemma6 h n) x y


-- Lemma 2.7

lemma7 :: Int -> Int -> Int -> Proof
{-@ lemma7 :: h:Nat -> n:Nat -> x:Nat
           -> {iack h n x <= iack h (n+1) x } @-}
lemma7 h n x
  | h == 0
  =   iack 0 n x
  ==. x
  ==. iack 0 (n+1) x
  *** QED

  | h > 0
  = iack h n x
  ==. ack n (iack (h-1) n x)
  <=. ack (n+1) (iack (h-1) n x)     ? lemma4_eq n (iack (h-1) n x)
  <=. ack (n+1) (iack (h-1) (n+1) x) ? (  lemma7 (h-1) n x
                                      ==> lemma3_eq (n+1) (iack (h-1) n x) (iack (h-1) (n+1) x)
                                        )
  <=. iack h (n+1) x
  *** QED



-- | Lemma 9


lemma9 :: Int -> Int -> Int -> Proof
{-@ lemma9 :: n:Pos -> x:Nat -> l:{Int | l < x + 2 }
           -> { x + l < ack n x } @-}
lemma9 n x l
  | x == 0
  = ack n 0 ==. 2 *** QED
  | n == 1
  = x + l <. ack 1 x ? lemma9_helper x l *** QED
  | otherwise
  = ack n x
  >. ack 1 x ? lemma4_gen 1 n x
  >. x+l     ? lemma9_helper x l
  *** QED


lemma9_helper :: Int -> Int -> Proof
{-@ lemma9_helper  :: x:Nat -> l:{Int | l < x + 2 }
            -> { x + l < ack 1 x } @-}
lemma9_helper x l
  | x == 0
  = ack 1 0 ==. 2 *** QED
  | x > 0
  = ack 1 x
  ==. ack 0 (ack 1 (x-1))
  ==. ack 1 (x-1) + 2
   >. x + l                ? lemma9_helper (x-1) (l-1)
  *** QED

-- | Lemma 2.10

lemma10 :: Int -> Int -> Int -> Proof
{-@ lemma10 :: n:Nat -> x:Pos -> l:{Nat | 2 * l < x}
            -> {iack l n x < ack (n+1) x } @-}
lemma10 n x l
  | n == 0
  =   iack l 0 x
  ==. x + 2 * l       ? lemma10_zero l x
   <. 2 + 2 * x
   <. ack 1 x         ? lemma10_one x
  *** QED
  | l == 0
  =   iack 0 n x
  ==. x
  <. ack (n+1) x     ? lemma2 (n+1) x
  *** QED
  | otherwise
  =   ack (n+1) x ==. iack x n 2                    ? def_eq n x
                  ==. ladder x n 2                  ? ladder_prop1 n x 2
                  ==. ladder ((x-l) + l) n 2
                  ==. ladder l n (ladder (x-l) n 2) ? ladder_prop2 l (x-l) n 2
                   >. ladder l n x                  ? (  lemma10_helper n x l
                                                   ==> ladder_prop1 n (x-l) 2
                                                   ==> ladder_prop3 x (ladder (x-l) n 2) n l
                                                    )
                   >. iack l n x                    ? ladder_prop1 n l x
                  *** QED


{-@ lemma10_zero :: l:Nat -> x:Nat -> { iack l 0 x == x + 2 * l } @-}
lemma10_zero :: Int -> Int -> Proof
lemma10_zero l x
  | l == 0
  = iack 0 0 x ==. x *** QED
  | l > 0
  =   iack l 0 x ==. ack 0 (iack (l-1) 0 x)
                 ==. (iack (l-1) 0 x) + 2
                 ==. (x + 2 * (l-1))  + 2       ? lemma10_zero (l-1) x
                 ==. x + 2*l
                 *** QED


{-@ lemma10_one :: x:Nat -> { ack 1 x == 2 + 2 * x} @-}
lemma10_one :: Int -> Proof
lemma10_one x
  | x == 0
  = ack 1 0 ==. 2 *** QED
  | otherwise
  =    ack 1 x ==. ack 0 (ack 1 (x-1))
               ==. 2 + (ack 1 (x-1))
               ==. 2 + (2 + 2 * (x-1))  ? lemma10_one (x-1)
               ==. 2 + 2 * x
               *** QED


lemma10_helper :: Int -> Int -> Int -> Proof
{-@ lemma10_helper :: n:Nat -> x:{Int | 0 < x } -> l:{Nat | 2 * l < x && x-l >=0}
            -> {  x < iack (x-l) n 2 } @-}
lemma10_helper n x l
  = iack (x-l) n 2 ==. ack (n+1) (x-l) ? def_eq n (x-l)
                    >. x               ? lemma9 (n+1) (x-l) l
                   *** QED



-- | Lader as helper definition and properties
{-@ axiomatize ladder @-}
{-@ ladder :: Nat -> {n:Int | 0 < n } -> Nat -> Nat @-}
ladder :: Int -> Int -> Int -> Int
ladder l n b
  | l == 0
  = b
  | otherwise
  = iack (ladder (l-1) n b) (n-1) 2


{-@ ladder_prop1 :: n:{Int | 0 < n} -> l:Nat -> x:Nat
                 -> {iack l n x == ladder l n x} / [l] @-}
ladder_prop1 :: Int -> Int -> Int -> Proof
ladder_prop1 n l x
    | l == 0
    = iack 0 n x ==. ladder 0 n x *** QED
    | otherwise
    =   iack l n x ==. ack n (iack (l-1) n x)
                   ==. ack n (ladder (l-1) n x) ? ladder_prop1 n (l-1) x
                   ==. iack (ladder (l-1) n x) (n-1) 2 ? def_eq (n-1) (ladder (l-1) n x)
                   ==. ladder l n x
                   *** QED


{-@ ladder_prop2 :: x:Nat -> y:Nat -> n:{Int | 0 < n} -> z:Nat
   -> { ladder (x + y) n z == ladder x n (ladder y n z)} / [x] @-}
ladder_prop2 :: Int -> Int -> Int -> Int -> Proof
ladder_prop2 x y n z
  | x == 0
  =  ladder 0 n (ladder y n z) ==. ladder y n z *** QED
  | otherwise
  =   ladder (x+y) n z ==. iack (ladder (x+y-1) n z) (n-1) 2
                       ==. iack (ladder (x-1) n (ladder y n z)) (n-1) 2 ? ladder_prop2 (x-1) y n z
                       ==. ladder x n (ladder y n z)
                       *** QED

{-@ ladder_prop3 :: x:Nat -> y:{Nat | x < y} -> n:{Int | 0 < n} -> l:Nat
   -> {ladder l n x < ladder l n y }  @-}
ladder_prop3 :: Int -> Int -> Int -> Int -> Proof
ladder_prop3 x y n l
  =  iack l n x <. iack l n y ? (  ladder_prop1 n l x
                                ==> ladder_prop1 n l y
                                ==> lemma6_gen l n x y
                                 ) *** QED


-- | Lemma 2.11

lemma11 :: Int -> Int -> Int -> Proof
{-@ lemma11 :: n:Nat -> x:Nat -> y:Nat -> { iack x n y < ack (n+1) (x+y) } @-}
lemma11 n x y
  =    ack (n+1) (x+y) ==. iack (x+y) n 2         ? def_eq n (x+y)
                       ==. iack x n (iack y n 2)  ? lemma11_helper n x y 2
                       ==. iack x n (ack (n+1) y) ? def_eq n y
                        >. iack x n y             ? (proof $
                                                          y <. ack (n+1) y ? lemma2 (n+1) y
                                                    ) ==> lemma6_gen x n y (ack (n+1) y)
                       *** QED

lemma11_helper :: Int -> Int -> Int -> Int -> Proof
{-@ lemma11_helper :: n:Nat -> x:Nat -> y:Nat -> z:Nat
             -> {iack (x+y) n z == iack x n (iack y n z) } / [x] @-}
lemma11_helper n x y z
  | x == 0
  = iack y n z ==. iack 0 n (iack y n z) *** QED
  | x>0
  =    iack (x+y) n z ==. ack n (iack (x+y-1) n z)
                     ==. ack n (iack (x-1) n (iack y n z)) ? lemma11_helper n (x-1) y z
                     ==. iack x n (iack y n z)
                     *** QED
