module AutoSize where

{-@ autosize List @-}
data List a = N | Cons a (List a)
nil = N
cons = Cons 

foo :: List a -> Int 
foo N = 0 
foo (Cons x xs) = 1 + foo xs 


{-@ autosize Exp @-}
data Exp = EConst Int | EBinOp Int Exp Exp 
expSize :: Exp -> Int
expSize (EConst _) = 0
expSize (EBinOp _ e1 e2) = 1 + (expSize e1) + (expSize e2)
