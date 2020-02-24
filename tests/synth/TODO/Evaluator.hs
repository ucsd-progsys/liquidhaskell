{-@ LIQUID "--typed-holes" @-}

import Language.Haskell.Liquid.Synthesize.Error

{-@ zero :: {v: Int | v == 0} @-}
zero :: Int 
zero = 0

{-@ one :: {v: Int | v == 1} @-}
one :: Int 
one = 1

{-@ two :: {v: Int | v == 2} @-}
two :: Int 
two = 2

data AST = Zero | One | Two | PlusNode AST AST | MinusNode AST AST | ProductNode AST AST

{-@ measure size @-}
{-@ size :: AST -> Nat @-}
size :: AST -> Int
size Zero 
    = 1
size One  
    = 1
size Two  
    = 1
size (PlusNode l r) 
    = 1 + size l + size r
size (MinusNode l r) 
    = 1 + size l + size r
size (ProductNode l r) 
    = 1 + size l + size r

{-@ measure result @-}
{-@ result :: AST -> Int @-}
result :: AST -> Int
result Zero 
    = 0
result One 
    = 1
result Two
    = 2
result (PlusNode l r)
    = result l + result r
result (MinusNode l r)
    = result l - result r
result (ProductNode l r)
    = result l * result r

{-@ type OpCode = { v: Int | v >= 0 && v <= 2 } @-}
type OpCode = Int

{-@ data PAST = IntNode { x :: Int } | OpNode { op :: OpCode, l :: PAST, r :: PAST } @-}
data PAST = IntNode { x :: Int } | OpNode { op :: OpCode, l :: PAST, r :: PAST }

{-@ sizeP :: PAST -> Nat @-}
sizeP :: PAST -> Int
sizeP (IntNode x)
    = 1
sizeP (OpNode op l r)
    = 1 + sizeP l + sizeP r

{-@ measure resultP @-}
{-@ resultP :: PAST -> Int @-}
resultP :: PAST -> Int
resultP (IntNode x)
    = x
resultP (OpNode op l r)
    | op == 0   = resultP l + resultP r
    | op == 1   = resultP l - resultP r
    | otherwise = resultP l * resultP r

{-@ transform :: x: AST -> { v: PAST | resultP v == result x } @-}
transform :: AST -> PAST
transform = _goal
-- transform x 
--     = case x of
--         Zero                -> IntNode zero
--         One                 -> IntNode one
--         Two                 -> IntNode two
--         PlusNode x6 x7      -> OpNode zero (transform x6) (transform x7)
--         MinusNode x15 x16   -> OpNode one (transform x15) (transform x16)
--         ProductNode x24 x25 -> OpNode two (transform x24) (transform x25)

    