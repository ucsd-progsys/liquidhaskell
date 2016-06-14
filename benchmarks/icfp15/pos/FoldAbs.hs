module Fold where

{-@ LIQUID "--no-termination" @-}
import Prelude hiding (foldr)

data Vec a = Nil | Cons a (Vec a)

{-@ 
efoldr :: forall <p :: (Vec a) -> b -> Prop, q :: a -> b -> b -> Prop>.
          {y::a, ys :: Vec a, acc:: b<p ys>, z :: {v:Vec a | v = Cons y ys && llen v = llen ys + 1}|- b<q y acc> <: b<p z>} 
         (x:a -> acc:b -> b<q x acc>)
      -> b<p Nil>
      -> xs:(Vec a)
      -> b<p xs>
@-}

efoldr :: (a -> b -> b) -> b -> Vec a -> b
efoldr op b Nil         = b
efoldr op b (Cons x xs) = x `op` efoldr op b xs

-- | We can encode the notion of length as an inductive measure @llen@ 

{-@ measure llen     :: forall a. Vec a -> Int 
    llen (Nil)       = 0 
    llen (Cons x xs) = 1 + llen(xs)
  @-}

-- | As a warmup, lets check that a /real/ length function indeed computes
-- the length of the list.


{-@ sizeOf :: xs:Vec a -> {v: Int | v = llen(xs)} @-}
sizeOf             :: Vec a -> Int
sizeOf Nil         = 0
sizeOf (Cons _ xs) = 1 + sizeOf xs



-------------------------------------------------------------------------
-- | Clients of `efold` ------------------------------------------------- 
-------------------------------------------------------------------------

-- | Finally, lets write a few /client/ functions that use `efoldr` to 
-- operate on the `Vec`s. 

-- | First: Computing the length using `efoldr`
{-@ size :: xs:Vec a -> {v: Int | v = llen xs} @-}
size :: Vec a -> Int
size = efoldr (\_ n -> n + 1) 0

-- | Second: Appending two lists using `efoldr`
{-@ app  :: xs: Vec a -> ys: Vec a -> {v: Vec a | llen v = llen xs + llen ys } @-} 
app xs ys = efoldr (\z zs -> Cons z zs) ys xs


            
