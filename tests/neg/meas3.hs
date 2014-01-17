module Meas () where


import Language.Haskell.Liquid.Prelude

--mylen []       = 0
--mylen (_:xs)   = 1 `plus` mylen xs

mylen xs = case xs of 
             []     -> 0
             (_:ys) -> 1 `plus` mylen ys


zs :: [Int]
zs = [1..100]

goo :: [dogbert] -> Int
goo _ = 1

bloo :: [Int] -> Int
bloo _ = 0

prop1 = liquidAssertB (n1 `eq` 0) 
  where n1 = mylen zs
