module Foo (goo) where 

goo :: Int 
goo = fac 5

fac :: Int -> Int 
fac n = if n == 0 then 1 else n * (fac (n-1))

