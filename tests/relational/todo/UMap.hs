{-# LANGUAGE ScopedTypeVariables #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module UMap where

import GHC.Types
import Prelude hiding (map)

type Proof = ()

type List a = [a]

{-@ reflect map @-}
{-@ map :: f1 : (Int -> Int) ->
           xs : List Int ->
           { r : List Int | len xs == len r }
@-}
map :: (Int -> Int) -> List Int -> List Int
map _ [] = []
map f (x:xs) = f x : map f xs

{-@ reflect mapRel @-}
{-@ mapRel :: f1:(Int -> Int) -> xs:List Int 
           -> f2:(Int -> Int) -> ys:List Int 
           -> { len xs <= len ys => len (map f1 xs) <= len (map f2 ys)}
@-}
mapRel :: (Int -> Int) -> List Int ->
          (Int -> Int) -> List Int -> Proof
mapRel _ [] _ [] = ()
mapRel f1 (x:xs) f2 [] = ()
mapRel f1 [] f2 (y:ys) = mapRel f1 [] f2 ys
mapRel f1 (x:xs) f2 (y:ys) = mapRel f1 xs f2 ys

{-@ relational map ~ map ::
                    {f1:(x1:Int -> Int) -> xs1:List Int -> List Int ~
                    f2:(x2:Int -> Int) -> xs2:List Int -> List Int 
                    | true :=> len xs1 <= len xs2 :=> len (r1 f1 xs1) <= len (r2 f2 xs2)} @-}
