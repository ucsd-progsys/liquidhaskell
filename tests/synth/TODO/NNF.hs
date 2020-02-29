{-@ LIQUID "--typed-holes" @-}

module NNF where

import Language.Haskell.Liquid.Synthesize.Error

{-@ data Expr [size] a = 
      Var a 
    | Not { x :: Expr a } 
    | And { al :: Expr a, ar :: Expr a } 
    | Or { ol :: Expr a, or :: Expr a }
    | Implies { il :: Expr a, ir :: Expr a } 
  @-}
data Expr a = Var a | Not (Expr a) | And (Expr a) (Expr a) | Or (Expr a) (Expr a) | Implies (Expr a) (Expr a)

{-@ measure size @-}
{-@ size :: Expr a -> {v: Int | v > 0} @-}
size :: Expr a -> Int
size Var{} = 1
size (Not e) = 1 + size e
size (And l r) = 1 + size l + size r
size (Or l r) = 1 + size l + size r
size (Implies l r) = 1 + size l + size r

{-@ data NExpr a = 
    NAtom { xx :: a, b :: Bool } 
    | NAnd { l :: NExpr a, r :: NExpr a }
    | NOr { ll :: NExpr a, rr :: NExpr a } 
  @-}
data NExpr a = NAtom a Bool | NAnd (NExpr a) (NExpr a) | NOr (NExpr a) (NExpr a)

{-@ inline imp @-}
{-@ imp :: x: Bool -> y: Bool -> { v: Bool | v <=> (x ==> y) } @-}
imp :: Bool -> Bool -> Bool
imp True  True  = True 
imp True  False = False
imp False True  = True
imp False False = True 

{-@ measure eval @-}
{-@ eval :: Expr a -> Bool @-}
eval (Var x) = store x
eval (Not e) = not (eval e)
eval (And l r) = eval l && eval r
eval (Or l r) = eval l || eval r
eval (Implies l r) = imp (eval l) (eval r)

{-@ reflect store @-} 
{-@ store :: a -> Bool @-}
store :: a -> Bool
store x = True

{-@ measure nEval @-}
{-@ nEval :: NExpr a -> Bool @-}
nEval (NAtom x neg) = if neg then not (store x) else store x
nEval (NAnd l r) = nEval l && nEval r
nEval (NOr l r) = nEval l || nEval r

{-@ true :: { v: Bool | v } @-}
true :: Bool
true = True

{-@ false :: { v: Bool | not v } @-}
false :: Bool
false = False

{-@ toNNF :: e: Expr a -> { v: NExpr a | nEval v == eval e } @-}
toNNF :: Expr a -> NExpr a
toNNF = _goal
-- toNNF e =
--     case e of
--         Var x2          -> NAtom x2 false
--         Not x6          -> 
--             case x6 of 
--                 Var x8          -> NAtom x8 true
--                 Not x12         -> toNNF x12
--                 And x16 x17     -> NOr (toNNF (Not x16)) (toNNF (Not x17))
--                 Or x26 x27      -> NAnd (toNNF (Not x26)) (toNNF (Not x27))
--                 Implies x36 x37 -> NAnd (toNNF x36) (toNNF (Not x37))
--         And x45 x46     -> NAnd (toNNF x45) (toNNF x46)
--         Or x53 x54      -> NOr (toNNF x53) (toNNF x54)
--         Implies x61 x62 -> NOr (toNNF x62) (toNNF (Not x61))

