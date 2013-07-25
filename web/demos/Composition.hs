{--! run liquid with no-termination -}

module Composition where

-- | Function Composition

-- Simple plus3 function
{-@ plus3' :: x:Int -> {v:Int | v = x + 3} @-}
plus3'     :: Int -> Int
plus3' x   = x + 3

-- Add 3 via function composition
{-@ plus3'' :: x:Int -> {v:Int | v = x + 3} @-}
plus3''     :: Int -> Int
plus3''     = (+1) `c` (+2)
  where c f g x = f (g x)


-- | Typing function composition

{-@ c :: forall < p :: b -> c -> Prop
                , q :: a -> b -> Prop>.
         (x:b -> c<p x>) 
      -> g:(x:a -> b<q x>) 
      -> y:a 
      -> exists[z:b<q y>].c<p z>
 @-}
c :: (b -> c) -> (a -> b) -> a -> c
c f g x = f (g x)

{-@ plus3 :: x:Int -> {v:Int | v = x + 3} @-}
plus3     :: Int -> Int
plus3     = (+1) `c` (+2)

{-@ qualif Plus(v:int,a:int,b:int): v = a + b @-}
