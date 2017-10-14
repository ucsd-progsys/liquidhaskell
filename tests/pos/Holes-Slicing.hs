module Foo () where

{-@ LIQUID "--savequery"      @-}
{-@ LIQUID "--noslice"        @-}
{-@ LIQUID "--maxparam=3"        @-}

{-@ measure isFoo :: A -> B -> Bool @-}
{-@ isFooF :: a:A -> b:B -> {v:Bool | v <=> isFoo a b} @-}
isFooF :: A -> B -> Bool
isFooF a b = undefined

{-@ prop1 :: u:A -> p:B -> {v : Int | isFoo u p <=> (v < 2) } @-}
prop1 :: A -> B -> Int
prop1 = undefined

{-@ foo :: A -> B -> _ @-}
foo :: A -> B -> Int
foo a b = if isFooF a b then 0 else 2 

data A
data B
