{-@ LIQUID "--reflection" @-}

module FunId where


{-@ funIdUnsafe :: g:(a -> b) -> { f:(a -> b) |  f == g } @-}
funIdUnsafe ::  (a -> b) -> (a -> b)
funIdUnsafe g = g ?? lemma ()

infixl 3 ??
(??) :: a -> b -> a 
x ?? _ = x 



{-@ funIdSafe :: g:(a -> b) -> { f:(a -> b) |  f == g } @-}
funIdSafe ::  (a -> b) -> (a -> b)
funIdSafe g = g ??? lemma ()

infixl 3 ???
(???) :: a -> b -> a 
{-@ (???) :: x:a -> b -> {v:a | v == x } @-}
x ??? _ = x 


lemma :: () -> () 
lemma _ = _ 
