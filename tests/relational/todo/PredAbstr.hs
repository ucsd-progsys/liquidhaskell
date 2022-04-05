nil :: a -> b -> (a, b)
nil a b = (a, b)

{-@ relational nil ~ nil :: a:_ -> b:_ -> _ ~ a':_ -> b':_ -> _ ~~ true @-}