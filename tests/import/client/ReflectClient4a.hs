{-@ LIQUID "--reflection" @-} 
{-@ LIQUID "--ple"        @-} 

module ReflectClient4a where

import ReflectLib4 

stupidity = [ undefined gapp ]

{-@ test1 :: { llen Nil == 0 } @-}
test1 = ()

{-@ test2 :: { llen (Cons 2 Nil) == 1 } @-}
test2 = ()

{-@ test3 :: { llen (Cons 1 (Cons 2 Nil)) == 2 } @-}
test3 = ()

{-@ test4 :: { app Nil Nil == Nil } @-}
test4 = () 

{-@ test5 :: { gapp Nil = Nil } @-}
test5 = ()


