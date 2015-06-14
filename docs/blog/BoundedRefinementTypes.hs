module BoundedRefinementTypes where
import Prelude hiding ((.))
import Language.Haskell.Liquid.Prelude


-- | Function Composition: First Attempt 

compose f g x = f (g x)   

{-@ incr :: x:Int -> {v:Int | v = x + 1} @-}
incr     :: Int -> Int 
incr x = x + 1

{-@ incr2 :: x:Int -> {v:Int | v = x + 2} @-}
incr2     :: Int -> Int 
incr2      = compose1 incr incr

{-@ compose1 :: (y:Int -> {z:Int | z = y + 1}) 
             -> (x:Int -> {z:Int | z = x + 1}) 
             ->  x:Int -> {z:Int | z = x + 2} @-}
compose1 :: (Int -> Int) -> (Int -> Int) -> Int -> Int 
compose1 f g x = f (g x)

{-@ incr3 :: x:Int -> {v:Int | v = x + 3} @-}
incr3    :: Int -> Int 
incr3      = compose1 incr incr2


-- | An Abstract Type for Compose: Second Attempt

{-@ compose2 :: forall <p :: b -> c -> Prop,
                        q :: a -> b -> Prop, 
                        r :: a -> c -> Prop>. 
                f:(y:b -> c<p y>)
             -> g:(x:a -> b<q x>)
             ->  x:a -> c<r x>
@-}    
compose2 :: (b -> c) -> (a -> b) -> a -> c
compose2 f g x = let z = g x in f z


{-@ incr2' :: x:Int -> {v:Int | v = x + 2} @-}
incr2'     :: Int -> Int 
incr2'      = compose2 incr incr


--  | Bound Abstract Refinements by the Chain Property: Final Type for Compose

chain :: (b -> c -> Bool) -> (a -> b -> Bool) 
      -> (a -> c -> Bool) ->  a -> b -> c -> Bool
chain p q r = \ x y z -> q x y ==> p y z ==> r x z

{-@ bound chain @-}

{-@
compose :: forall <p :: b -> c -> Prop,
                   q :: a -> b -> Prop, 
                   r :: a -> c -> Prop>. 
           (Chain b c a p q r)
        => (y:b -> c<p y>)
        -> (z:a -> b<q z>)
        ->  x:a -> c<r x>
@-}    

{-@ incr2'' :: x:Int -> {v:Int | v = x + 2} @-}
incr2''      = compose incr incr

{-@ incr3'' :: x:Int -> {v:Int | v = x + 3} @-}
incr3''      = compose incr2'' incr
