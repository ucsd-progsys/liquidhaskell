-- WITH-PLE 

module Hutton where

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

import Language.Haskell.Liquid.ProofCombinators

import Prelude hiding (length, head, tail, map, (++))

-- need to use a hand-rolled list type, it seems

data L a = N | C {hd :: a, tl :: L a}
{-@ data L [length] a = N | C {hd :: a, tl :: L a} @-}

length :: L a -> Int
{-@ length :: L a -> Nat @-}
{-@ measure length @-}
length N        = 0
length (C _ xs) = 1 + length xs

{-@ infix   ++ @-}
{-@ reflect ++ @-}
(++) :: L a-> L a -> L a
N        ++ ys = ys
(C x xs) ++ ys = C x (xs ++ ys)

-- huttons razor

data Expr = Val Int | Add Expr Expr
{-@ data Expr [height] = Val {theVal :: Int} | Add {summand1 :: Expr, summand2 :: Expr}  @-}


{-@ height :: Expr -> Nat @-}
{-@ measure height @-}
height :: Expr -> Int
height (Val _) = 0
height (Add e1 e2) = 1 + if height e1 > height e2 then  height e1 else height e2

{- @ eval :: e:Expr -> Int / [height e] @-}
{-@ reflect eval @-}
eval :: Expr -> Int
eval (Val n)   = n
eval (Add x y) = eval x + eval y

type Stack = L Int

type Code = L Op

data Op = PUSH Int | ADD
{-@ data Op = PUSH {thePushed :: Int} | ADD @-}

{-@ reflect exec @-}
exec :: Code -> Stack -> Stack
exec N s                          = s
exec (C (PUSH n) c) s             = exec c (C n s)
exec (C ADD      c) (C m (C n s)) = exec c (C (n+m) s)
exec (C ADD      c) (C n N)       = N -- default case added
exec (C ADD      c) N             = N -- default case added (need to be sparate cases)

{-@ reflect comp @-}
comp :: Expr -> Code
comp (Val n)   = C (PUSH n) N
comp (Add x y) = (comp x ++ comp y) ++ (C ADD N)

-- Proofs

{-@ lemma_assoc4 :: as:L a -> bs:L a -> cs:L a -> ds:L a 
                 -> {((as ++ bs) ++ cs) ++ ds  == as ++ (bs ++ (cs ++ ds)) }
  @-}
lemma_assoc4 :: L a -> L a -> L a -> L a -> Proof 
lemma_assoc4 _ _ _ _ = undefined

{-@ lemma_app_nil :: x:a -> ys:L a -> { (C x N) ++ ys = C x ys } @-}
lemma_app_nil :: a -> L a -> Proof
lemma_app_nil _ _ = () 

{-@ correctness :: e:Expr -> c:Code -> s:Stack ->
                  { exec (comp e ++ c) s = exec c (C (eval e) s) }
@-}
correctness :: Expr -> Code -> Stack -> Proof
correctness (Val n) c s 
  = [
    --   exec (comp (Val n) ++ c) s
    -- ==. exec ((C (PUSH n) N) ++ c) s
    -- ==. exec ((C (PUSH n) (N ++ c))) s
    -- ==. exec (C (PUSH n) c) s
    -- ==. exec c (C n s)
    -- ==. exec c (C (eval (Val n)) s)
    ] *** QED


correctness (Add e1 e2) c s 
  = [ 
  --    exec (comp (Add e1 e2) ++ c) s 
  -- ==. exec (((comp e1 ++ comp e2) ++ (C ADD N)) ++ c) s
  -- ==. exec (comp e1 ++ (comp e2 ++ ((C ADD N) ++ c))) s
      lemma_assoc4 (comp e1) (comp e2) (C ADD N) c
  -- ==. (exec (comp e2 ++ ((C ADD N) ++ c)) (C (eval e1) s))
    , correctness e1 (comp e2 ++ ((C ADD N) ++ c)) s
  -- ==. exec ((C ADD N) ++ c) (C (eval e2) (C (eval e1) s))
    , correctness e2 ((C ADD N) ++ c) (C (eval e1) s)
  -- ==. exec (C ADD c) (C (eval e2) (C (eval e1) s))
    , lemma_app_nil ADD c
  -- ==. exec c (C (eval e1 + eval e2) s)
  -- ==. exec c (C (eval (Add e1 e2)) s)
  ] *** QED    

