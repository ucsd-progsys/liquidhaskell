module Spec where 

data Foo = Foo Int 
{-@ data Foo = Foo {unfoo :: {v:Int | 0 < v } @-} 
