module Meas5 () where

import Language.Haskell.Liquid.Prelude

{-@ include <len.hquals> @-}

mylen          :: [a] -> Int
mylen []       = 0
mylen (_:xs)   = 1 + mylen xs


mymap f []     = []
mymap f (x:xs) = (f x) : (mymap f xs)


{-@ myreverse :: xs:_ -> {v:_ | len v = len xs} @-} 
myreverse = go []
  where 
    {-@ go :: acc:_ -> xs:_ -> {v:_ | len v = len acc + len xs} @-}
    go acc (x:xs) = go (x:acc) xs
    go acc []     = acc
    
{-@ myapp :: xs:_ -> ys:_ -> {v:_ | len v = len xs + len ys} @-}
myapp [] ys     = ys
myapp (x:xs) ys = x:(myapp xs ys)

zs :: [Int]
zs = [1..100]

zs' :: [Int]
zs' = [500..1000]

prop2 = liquidAssertB (n1 == n2) 
  where n1 = mylen zs
        n2 = mylen $ mymap (+ 1) zs 

prop3 = liquidAssertB (n1 == n2) 
  where n1 = mylen zs
        n2 = mylen $ myreverse zs 

prop4 = liquidAssertB ((n1 + n2) == n3) 
  where n1 = mylen zs
        n2 = mylen zs'
        n3 = mylen $ myapp zs zs' 

prop5 = liquidAssertB (length zs'' == length zs) 
        where zs'' = safeZipWith (+) zs (myreverse zs)
