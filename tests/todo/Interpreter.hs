module Interpreter where 
{-@ LIQUID "--totality" @-}
{-@ LIQUID "--real" @-}

data BinOp a = Plus | Times

data Exp a  = EConst Int | EBinOp (BinOp a) (Exp a) (Exp a)

data Instr a = IConst Int | IBinOp (BinOp a)

data List a = Nil | Cons a (List a)

type Prog  = List (Instr Int)
type Stack = List Int

{-@ measure binOpDenote @-}
binOpDenote :: Int -> Int -> BinOp a -> Int 
binOpDenote x y Plus  = (x+y)
binOpDenote x y Times = (x*y)

{-@ measure expDenote @-}
expDenote :: Exp a -> Int 
expDenote (EConst n)       = n
expDenote (EBinOp b e1 e2) = binOpDenote (expDenote e1) (expDenote e2) b


{- HERE HERE -}
{- measure instrDenote @-}
instrDenote :: Stack -> Instr a -> Maybe Stack
instrDenote s       (IConst n) = Just (cons n s)
instrDenote (Cons x (Cons y s)) (IBinOp b) = Just (cons (binOpDenote x y b) s)
instrDenote _        _         = Nothing

{-
{- measure progDenote :: Stack -> Prog -> Maybe Stack @-}
progDenote :: Stack -> Prog -> Maybe Stack
progDenote s Nil = Just s
progDenote s (Cons x xs) | Just s' <- instrDenote s x = progDenote s' xs
                         | otherwise                  = Nothing

{- compile :: e:Exp -> {v:Prog | (progDenote Nil v) == Nothing } @-}
{- compile :: e:Exp -> {v:Prog | (progDenote Nil v) == Just (Cons (expDenote e) Nil)} @-}
compile :: Exp -> Prog
compile (EConst n)       = single (IConst n)  
compile (EBinOp b e1 e2) = compile e2 `append` compile e1 `append` (single $ IBinOp b) 

-}
-- List operations
{-@ autosize Exp @-}
{-@ autosize List @-}

(Cons x xs) `append` ys = cons x $ append xs ys
Nil         `append` ys = ys 

emp      = Nil
single x = Cons x Nil
cons     = Cons 

