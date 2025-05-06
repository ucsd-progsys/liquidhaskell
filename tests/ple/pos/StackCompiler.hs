{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}

{-@ LIQUID "--ple"           @-}
{-@ LIQUID "--etabeta"       @-}
{-@ LIQUID "--reflection"    @-}
{-@ LIQUID "--dependantcase" @-}

module StackCompiler where

import Prelude hiding ((.))
import Language.Haskell.Liquid.ProofCombinators

{-@ assume reflect id as myid @-}
{-@ reflect $  @-}
{-@ infix $    @-}

{-@ reflect myid @-}
myid :: a -> a
myid x = x

{-@ reflect .  @-}
{-@ infix .    @-}
infixr 9 .
(.) :: (b -> c) -> (a -> b) -> a -> c
(.) f g x = f (g x)

data Expr where
  EConst :: Int -> Expr
  EAdd   :: Expr -> Expr -> Expr
  EMul   :: Expr -> Expr -> Expr
  ENeg   :: Expr -> Expr

{-@ reflect eval @-}
eval :: Expr -> Int
eval (EConst x) = x
eval (EAdd e1 e2) = eval e1 + eval e2
eval (EMul e1 e2) = eval e1 * eval e2
eval (ENeg e)     = - (eval e)

type Stack = [Int]

data OpCode where
  OpPush :: Int -> OpCode
  OpAdd :: OpCode
  OpMul :: OpCode
  deriving Show


{-@ reflect push @-}
push :: Int -> Stack -> Stack
push v s = v : s

{-@ reflect execOpCode @-}
{-@ execOpCode :: o:OpCode -> { v:Stack | len v >= minStackSize o } -> Stack @-}
execOpCode :: OpCode -> Stack -> Stack
execOpCode (OpPush x) = push x
execOpCode OpAdd      = \case (x : y : xs) -> (y + x) : xs
execOpCode OpMul      = \case (x : y : xs) -> (y * x) : xs

{-@ reflect minStackSize @-}
minStackSize :: OpCode -> Int
minStackSize (OpPush x) = 0
minStackSize _          = 2

data Program where
{-@ PNil :: Prop (Program id) @-}
  PNil :: Program
{-@ PCons :: op:OpCode
          -> p:(Stack -> { v:Stack | len v >= minStackSize op }) -> Prop (Program p)
          -> Prop (Program (execOpCode op . p)) @-}
  PCons :: OpCode -> (Stack -> Stack) -> Program -> Program
data PROGRAM = Program (Stack -> Stack)

{-@ reflect compose @-}
{-@ compose :: p1:(Stack -> Stack) -> p2:(Stack -> Stack)
            -> Prop (Program p1) -> Prop (Program p2)
            -> Prop (Program (p2 . p1)) @-}
compose :: (Stack -> Stack) -> (Stack -> Stack) -> Program -> Program -> Program
compose s1 s2 p1 PNil                   = p1
compose s1 s2 p1 (PCons cmd srest rest) =
  PCons cmd (srest . s1) (compose s1 srest p1 rest)

{-@ compile :: e:Expr -> Prop (Program (push $ eval e)) @-}
compile :: Expr -> Program
compile (EConst x)   = PCons (OpPush x) id PNil
compile (EAdd e1 e2) =
  PCons
    OpAdd
    ((push $ eval e1) . (push $ eval e2))
    (compose (push $ eval e2) (push $ eval e1) (compile e2) (compile e1))
compile (EMul e1 e2) =
  PCons
    OpMul
    ((push $ eval e1) . (push $ eval e2))
    (compose (push $ eval e2) (push $ eval e1) (compile e2) (compile e1))
compile (ENeg e)     =
  PCons
    OpMul
    ((push $ -1) . (push $ eval e))
    (PCons (OpPush $ -1) (push $ eval e) (compile e))
