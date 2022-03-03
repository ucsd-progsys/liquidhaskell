module SpecLib where 

data Foo = FooDC Int 
{-@ data Foo = FooDC {unfoo :: {v:Int | 0 < v }} @-} 

{-@ measure cfun @-}
{-@ cfun :: Foo -> {v:Int | 0 < v} @-} 
cfun :: Foo -> Int 
cfun (FooDC x) = x
