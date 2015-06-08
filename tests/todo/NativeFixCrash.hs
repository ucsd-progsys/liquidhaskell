module Interpreter where 

data List a = Nil | Cons a (List a)

single x = Cons x Nil
cons     = Cons 


