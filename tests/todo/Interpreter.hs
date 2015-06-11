module Interpreter where 
{-@ LIQUID "--totality" @-}

data BinOp = Plus | Times

data Exp   = EConst Int | EBinOp BinOp Exp Exp

data Instr = IConst Int | IBinOp BinOp

data List a = Nil | Cons a (List a)

type Prog  = List Instr
type Stack = List Int

binOpDenote Plus  = (+)
binOpDenote Times = (*)

expDenote :: Exp -> Int 
expDenote (EConst n)       = n
expDenote (EBinOp b e1 e2) = (binOpDenote b) (expDenote e1) (expDenote e2)

instrDenote :: Stack -> Instr -> Maybe Stack
instrDenote s       (IConst n) = Just (cons n s)
instrDenote (Cons x (Cons y s)) (IBinOp b) = Just (cons ((binOpDenote b) x y) s)
instrDenote _        _         = Nothing

{-@ measure progDenote :: Stack -> Prog -> Maybe Stack @-}
progDenote :: Stack -> Prog -> Maybe Stack
progDenote s Nil = Just s
progDenote s (Cons x xs) | Just s' <- instrDenote s x = progDenote s' xs
                         | otherwise                  = Nothing

{- compile :: e:Exp -> {v:Prog | (progDenote Nil v) == Nothing } @-}
{-@ compile :: e:Exp -> {v:Prog | (progDenote Nil v) == Just (Cons (expDenote e) Nil)} @-}
compile :: Exp -> Prog
compile (EConst n)       = single (IConst n)  
compile (EBinOp b e1 e2) = compile e2 `append` compile e1 `append` (single $ IBinOp b) 


-- List operations
{-@ autosize Exp @-}
{-@ autosize List @-}

(Cons x xs) `append` ys = cons x $ append xs ys
Nil         `append` ys = ys 

emp      = Nil
single x = Cons x Nil
cons     = Cons 

