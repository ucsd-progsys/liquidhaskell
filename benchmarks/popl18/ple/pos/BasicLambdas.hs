{-@ LIQUID "--reflection" @-}

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



{-@ reflect bind @-}
bind :: a -> (a -> b) ->  b
bind x f = f x

{-@ helper :: m:a -> {v: a |  v == bind m (\x:a -> m)} @-}
helper :: a -> a
helper m = bind m h
  where
    h   =  \x -> m



{-@ reflect id @-}
id :: a -> a
id x = x



{-@ assume fun_eq :: f:(a -> b) -> g:(a -> b) 
      -> (x:a -> {f x == g x}) -> {f == g} 
  @-}   
fun_eq :: (a -> b) -> (a -> b) -> (a -> Proof) -> Proof   
fun_eq _ _ _ = trivial     


 
