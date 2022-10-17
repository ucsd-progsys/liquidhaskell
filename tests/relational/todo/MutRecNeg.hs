module MutRec where

{-@ relational foo ~ foo :: n1:_ -> _ ~ n2:_ -> _ ~~ true => bar  @-}
foo :: Bool
foo = True


{-@ relational bar ~ bar :: n1:_ -> _ ~ n2:_ -> _ ~~ true => r1 n1 = 0 && r2 n2 = 0 @-}
bar :: Bool
bar = True