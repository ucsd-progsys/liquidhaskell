{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-warnings"    @-}
{-@ LIQUID "--no-termination" @-}


module Foo (insertSort) where

data List a = N | C a (List a)

infixr 9 `C`

{-@ ifoldr :: forall a b <p :: List a -> b -> Prop>. 
                 (xs:_ -> x:_ -> b<p xs> -> b<p(C x xs)>) 
               -> b<p N> 
               -> ys:List a
               -> b<p ys>                            @-}
ifoldr :: (List a -> a -> b -> b) -> b -> List a -> b
ifoldr = undefined

{-@ data List a <p :: a -> a -> Prop> 
     = N | C {x :: a, xs :: List<p> a<p x>} @-}

{-@ type IncrList a = List <{\x y -> x <= y}> a @-} 

{-@ insert :: a -> IncrList a -> IncrList a @-}
insert :: a -> List a -> List a
insert = undefined

{-@ insertSort      :: xs:List a -> {v:IncrList a | true } @-}
insertSort :: List a -> List a
insertSort = undefined



nil :: List a 
nil = N
