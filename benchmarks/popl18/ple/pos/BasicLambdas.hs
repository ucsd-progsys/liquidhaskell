
{-@ LIQUID "--higherorder"      @-}
{-@ LIQUID "--exact-data-cons" @-}

{- LIQUID "--automatic-instances=liquidinstances" @-}

module BasicLambda where

import Language.Haskell.Liquid.ProofCombinators

import Prelude hiding (map, id)


{-@ lamEq :: a -> {v: Proof | (\y:a -> y) == (\x:a -> x)} @-}
lamEq :: a -> Proof
lamEq _ = trivial 

{-@ funEq :: m1:a  -> m2:{v:a | v == m1} -> {v: Proof | (\y:a -> m1) == (\y:a -> m2)} @-}
funEq :: a  -> a -> Proof
funEq _ _ = trivial


{-@ funIdEq :: m1:a  -> m2:{v:a | v == m1} -> {v: Proof | (\x:a -> (\y:a -> y)) == (\z:a -> (\x:a -> x))} @-}
funIdEq :: a  -> a -> Proof
funIdEq _ _ = trivial

{-@ funApp :: m1:a  -> m2:{v:a | v == m1} -> {v: Proof | (\y:a -> m1) (m1) == ((\x:a -> m2)) (m2) } @-}
funApp :: a  -> a -> Proof
funApp _ _ = trivial



{-@ axiomatize bind @-}
bind :: a -> (a -> b) ->  b
bind x f = f x

{-@ helper :: m:a -> {v: a |  v == bind m (\x:a -> m)} @-}
helper :: a -> a
helper m = bind m h
  where
    h   =  \x -> m



{-@ axiomatize id @-}
id :: a -> a
id x = x


{-@ fmap_id' 
  :: x:(r -> a)
  -> {v:Proof | (\r:r -> id (x r)) ==  (\r:r -> (x r) ) } @-}
fmap_id' :: (r -> a) ->  Proof
fmap_id' x
   =   fun_eq (\rrr1 -> x rrr1) (\rrr2 -> id (x rrr2)) (\r -> x  r ==. id (x r) *** QED)



{-@ assume fun_eq :: f:(a -> b) -> g:(a -> b) 
   -> (x:a -> {f x == g x}) -> {f == g} 
  @-}   
fun_eq :: (a -> b) -> (a -> b) -> (a -> Proof) -> Proof   
fun_eq _ _ _ = trivial     


 
