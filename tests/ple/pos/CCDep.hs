-- Implementation in LH of Calculating Dependently-Typed Compilers
-- https://people.cs.nott.ac.uk/pszgmh/well-typed.pdf

{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}

{-@ LIQUID "--ple"               @-}
{-@ LIQUID "--reflection"        @-}
{-@ LIQUID "--max-case-expand=4" @-}

module CCDep where

import Prelude

import Language.Haskell.Liquid.ProofCombinators

{-@ infix :  @-}
{-@ infix || @-}
{-@ infix && @-}
{-@ infix ++ @-}

{-@ reflect ror @-}
{-@ assume reflect || as ror @-}
ror :: Bool -> Bool -> Bool
ror True _ = True
ror _ True = True
ror _ _    = False

{-@ reflect rand @-}
{-@ assume reflect && as rand @-}
rand :: Bool -> Bool -> Bool
rand True True = True
rand _ _       = False

{-@ reflect plusplus @-}
{-@ assume reflect ++ as plusplus @-}
plusplus :: [a] -> [a] -> [a]
plusplus []     ys = ys
plusplus (x:xs) ys = x : xs `plusplus` ys

{-@ reflect append @-}
append = (:)

data Expr where
{-@ EVal :: Nat -> Prop (Expr False) @-}
    EVal :: Int -> Expr
{-@ EAdd :: a:Bool -> b:Bool
        -> Prop (Expr a) -> Prop (Expr b)
        -> Prop (Expr (a || b)) @-}
    EAdd :: Bool -> Bool -> Expr -> Expr -> Expr
{-@ EThrow :: Prop (Expr True) @-}
    EThrow :: Expr
{-@ ECatch :: a:Bool -> b:Bool
           -> Prop (Expr a) -> Prop (Expr b)
           -> Prop (Expr (a && b)) @-}
    ECatch :: Bool -> Bool -> Expr -> Expr -> Expr
data EXPR = Expr Bool

{-@ reflect evalM @-}
{-@ evalM :: b:Bool -> Prop (Expr b) -> Maybe Nat @-}
evalM :: Bool -> Expr -> Maybe Int
evalM b (EVal n)             = Just n
evalM b (EAdd b1 b2 e1 e2)   = do
    n1 <- evalM b1 e1
    n2 <- evalM b2 e2
    pure $ n1 + n2
evalM b EThrow               = Nothing
evalM b (ECatch b1 b2 e1 e2) = case evalM b1 e1 of
    Just n  -> Just n
    Nothing -> evalM b2 e2

{-@ eval :: Prop (Expr False) -> Nat @-}
eval :: Expr -> Int
eval (EVal n)                   = n
eval (EAdd False False e1 e2)   = eval e1 + eval e2
eval (ECatch False b2    e1 e2) = eval e1
eval (ECatch True  False e1 e2) = case evalM True e1 of
  Just n  -> n
  Nothing -> eval e2

data Ty where
    TNat :: Ty
    THan :: [Ty] -> [Ty] -> Ty

data Code where
{-@ CPush :: s:[Ty] -> s':[Ty]
          -> Nat -> Prop (Code (TNat : s) s')
          -> Prop (Code s s') @-}
    CPush :: [Ty] -> [Ty] -> Int -> Code -> Code
{-@ CAdd :: s:[Ty] -> s':[Ty]
         -> Prop (Code (TNat : s) s')
         -> Prop (Code (TNat : TNat : s) s') @-}
    CAdd :: [Ty] -> [Ty] -> Code -> Code
{-@ CThrow :: s:[Ty] -> s':[Ty] -> s'':[Ty]
           -> Prop (Code (s'' ++ (THan s s' : s)) s') @-}
    CThrow :: [Ty] -> [Ty] -> [Ty] -> Code
{-@ CMark :: s:[Ty] -> s':[Ty]
          -> Prop (Code s s')
          -> Prop (Code ((THan s s') : s) s')
          -> Prop (Code s s') @-}
    CMark :: [Ty] -> [Ty] -> Code -> Code -> Code
{-@ CUnmark :: s:[Ty] -> s':[Ty] -> k:Ty
            -> Prop (Code (append k s) s')
            -> Prop (Code (append k (THan s s' : s)) s') @-}
-- TODO: BUG int the parser ignoring k if using :
    CUnmark :: [Ty] -> [Ty] -> Ty -> Code -> Code
{-@ CHalt :: s:[Ty] -> Prop (Code s s) @-}
    CHalt :: [Ty] -> Code
data CODE = Code [Ty] [Ty]

data Val where
{-@ VNat :: Nat -> Prop (Val TNat) @-}
    VNat :: Int -> Val
{-@ VHan :: s:[Ty] -> s':[Ty]
         -> Prop (Code s s')
         -> Prop (Val (THan s s')) @-}
    VHan :: [Ty] -> [Ty] -> Code -> Val
data VAL = Val Ty

{-@ compM :: b:Bool -> s:[Ty] -> s':[Ty] -> s'':[Ty]
          -> Prop (Expr b) -> Prop (Code (TNat : (s'' ++ (THan s s' : s))) s')
          -> Prop (Code (s'' ++ (THan s s' : s)) s') @-}
compM :: Bool -> [Ty] -> [Ty] -> [Ty] -> Expr -> Code -> Code
compM b s s' s'' (EVal n)             c = CPush (s'' ++ (THan s s' : s)) s' n c
compM b s s' s'' (EAdd b1 b2 e1 e2)   c = compM b1 s s' s'' e1
                                            (compM b2 s s' (TNat : s'') e2
                                                (CAdd (s'' ++ (THan s s' : s)) s' c))
compM b s s' s'' EThrow               c = CThrow s s' s''
compM b s s' s'' (ECatch b1 b2 e1 e2) c = CMark (s'' ++ (THan s s' : s)) s'
                                            (compM b2 s s' s'' e2 c)
                                            (compM b1 (s'' ++ (THan s s' : s)) s' [] e1
                                                (CUnmark (s'' ++ (THan s s' : s)) s' TNat c))

{-@ comp :: s:[Ty] -> s':[Ty]
         -> Prop (Expr False) -> Prop (Code (TNat : s) s')
         -> Prop (Code s s') @-}
comp :: [Ty] -> [Ty] -> Expr -> Code -> Code
comp s s' (EVal n)                  c = CPush s s' n c
comp s s' (EAdd False False e1 e2)  c = comp s s' e1 (comp (TNat : s) s' e2 (CAdd s s' c))
comp s s' (ECatch False b2 e1 e2)   c = comp s s' e1 c
comp s s' (ECatch True False e1 e2) c = CMark s s'
                                            (comp s s' e2 c)
                                            (compM True s s' [] e1 (CUnmark s s' TNat c))

{-@ compile :: s:[Ty] -> Prop (Expr False) -> Prop (Code s (TNat : s)) @-}
compile :: [Ty] -> Expr -> Code
compile s e = comp s (TNat : s) e (CHalt (TNat : s))

data Stack where
{-@ SNil :: Prop (Stack []) @-}
    SNil :: Stack
{-@ SCons :: t:Ty -> ts:[Ty]
          -> Prop (Val t) -> Prop (Stack ts)
          -> Prop (Stack (append t ts)) @-}
    SCons :: Ty -> [Ty] -> Val -> Stack -> Stack
data STACK = Stack [Ty]

{-@ exec :: s:[Ty] -> s':[Ty] -> Prop (Code s s') -> Prop (Stack s) -> Prop (Stack s') @-}
exec :: [Ty] -> [Ty] -> Code -> Stack -> Stack
exec s s' (CPush _ _ n c)  i = exec (TNat : s) s' c (SCons TNat s (VNat n) i)
exec (TNat : TNat : s)  s' (CAdd _ _ c) (SCons _ _ (VNat n) (SCons _ _ (VNat m) i)) =
    exec (TNat : s) s' c (SCons TNat s (VNat (n + m)) i)
exec s s' (CThrow a b c) i = failE a b c i
exec s s' (CMark _ _ c1 c2) i = exec (THan s s' : s) s' c2 (SCons (THan s s') s (VHan s s' c1) i)
exec _ s' (CUnmark _ _ _ c) i = case i of
    SCons t _ v (SCons _ s _ i) -> exec (t : s) s' c (SCons t s v i)
exec s s' (CHalt _) i  = i

-- They don't prove termination in the paper :)
{-@ lazy failE @-}
{-@ failE :: s:[Ty] -> s':[Ty] -> s'':[Ty] -> Prop (Stack (s'' ++ THan s s' : s)) -> Prop (Stack s') @-}
failE :: [Ty] -> [Ty] -> [Ty] -> Stack -> Stack
failE _ _  []        (SCons _ _ (VHan s s' h) i) = exec s s' h i
failE s s' (_ : s'') (SCons _ _ _             i) = failE s s' s'' i
