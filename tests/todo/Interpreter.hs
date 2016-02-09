module Interpreter where 
{-@ LIQUID "--totality" @-}
data BinOp a = Plus | Times

data Exp a  = EConst Int | EBinOp (BinOp a) (Exp a) (Exp a)

data Instr a = IConst Int | IBinOp (BinOp a)

data List a = Nil | Cons a (List a)


{-@ autosize Prog @-}
data Prog a = Emp | PInst (Instr a) (Prog a)
type Stack = List Int

data SMaybe a = SNothing a | SJust a

{-@ measure binOpDenote @-}
binOpDenote :: Int -> Int -> BinOp a -> Int 
binOpDenote x y Plus  = (x+y)
binOpDenote x y Times = (x*y)

{-@ measure expDenote @-}
expDenote :: Exp a -> Int 
expDenote (EConst n)       = n
expDenote (EBinOp b e1 e2) = binOpDenote (expDenote e1) (expDenote e2) b

{-@foo :: s:Stack -> {v:SMaybe Stack| v = SNothing s || v = SJust s } @-}
foo :: Stack -> SMaybe Stack
foo = undefined 

{-@ measure instrDenote @-}
instrDenote :: Stack -> Instr a -> SMaybe Stack
{-@ instrDenote :: s:Stack -> i:{v:Instr a | isIBinOp v => lenL s >= 2} 
                -> {v:SMaybe {st:Stack | if (isIBinOp i) then (lenL st = lenL s - 1) else (lenL st = lenL s + 1)} | v = instrDenote s i} @-}
instrDenote s (IConst n) = SJust (Cons n s)
instrDenote s (IBinOp b) = 
	let x  = headL s in 
	let s1 = tailL s in 
	let y  = headL s1 in 
	let s2 = tailL s1 in 
	SJust (Cons (binOpDenote x y b) s2)


{-@ invariant {v:Prog a | binOps v >= 0} @-}
{-@ measure binOps @-}
binOps :: Prog a -> Int 
binOps Emp = 0 
binOps (PInst x xs) = if isIBinOp x then 1 + (binOps xs) else binOps xs 



{- measure progDenote :: Stack -> Prog -> SMaybe Stack @-}
{-@ measure progDenote @-}
{-@ Decrease progDenote 2 @-}
progDenote :: Stack -> Prog a -> SMaybe Stack
{-@ progDenote :: s:Stack -> p:{v:Prog a | lenL s >= 2 * binOps v }  -> {v: SMaybe Stack | v = progDenote s p} @-}
progDenote s Emp = SJust s
progDenote s (PInst x xs) = SNothing s 
{-
progDenote s (PInst x xs) | SJust s' <- instrDenote s x = progDenote s' xs
                          | otherwise                   = SNothing s
-}

{-
{- compile :: e:Exp -> {v:Prog | (progDenote Nil v) == Nothing } @-}
{- compile :: e:Exp -> {v:Prog | (progDenote Nil v) == Just (Cons (expDenote e) Nil)} @-}
compile :: Exp -> Prog
compile (EConst n)       = single (IConst n)  
compile (EBinOp b e1 e2) = compile e2 `append` compile e1 `append` (single $ IBinOp b) 

-}



-- Hard Wire the measures so that I can provide exact types for Nil and Cons
{-@ SNothing :: s:s -> {v:SMaybe s | v = SNothing s && not (isSJust v)} @-}
{-@ SJust    :: s:s -> {v:SMaybe s | v = SJust s && (isSJust v) && (fromSJust v = s)} @-}
{-@ Cons     :: x:a -> xs:List a -> {v:List a | v = Cons x xs && headL v = x && tailL v = xs && lenL v = 1 + lenL xs} @-}
{-@ Nil      :: {v:List a | v = Nil  && lenL v = 0} @-}
iconst = IConst


{-@ measure isSJust :: SMaybe a -> Prop @-}
{-@ isSJust :: x:SMaybe a -> {v:Bool | Prop v <=> isSJust x}  @-}
isSJust (SJust _) = True 
isSJust (SNothing _ ) = False

{-@ measure fromSJust :: SMaybe a -> a @-}
{-@ fromSJust :: x:{v:SMaybe a | isSJust v} -> {v:a | v = fromSJust x}  @-}
fromSJust (SJust x) = x

{-@ measure isIBinOp @-}
isIBinOp (IBinOp _) = True
isIBinOp _          = False

{-@ measure headL :: List a -> a @-}
{-@ headL :: xs:{v:List a | lenL v > 0} -> {v:a | v = headL xs} @-}
headL :: List a -> a
headL (Cons x _) = x

{-@ measure tailL :: List a -> List a @-}
{-@ tailL :: xs:{v:List a | lenL v > 0} -> {v: List a | v = tailL xs && lenL v = lenL xs - 1} @-}
tailL :: List a -> List a
tailL (Cons _ xs) = xs


{-@ measure lenL :: List a -> Int @-}
{-@ invariant {v:List a | lenL v >= 0 } @-}
lenL :: List a -> Int 
lenL (Cons _ xs) = 1 + lenL xs 
lenL Nil         = 0 



-- List operations
{-@ autosize Exp @-}
{-@ data List [lenL] @-}

(Cons x xs) `append` ys = cons x $ append xs ys
Nil         `append` ys = ys 

emp      = Nil
single x = Cons x Nil
cons x xs = Cons x xs

