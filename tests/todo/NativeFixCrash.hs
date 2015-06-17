module Interpreter where 

data Instr = I

data List a = Nil | Cons a (List a)

type Prog  = List Instr
type Stack = List Int

{-@ measure progDenote :: Stack -> Prog -> Maybe Stack @-}
progDenote :: Stack -> Prog -> Maybe Stack
progDenote s Nil = Just s
progDenote s (Cons x xs) | Just s' <- Just s  = progDenote s' xs

