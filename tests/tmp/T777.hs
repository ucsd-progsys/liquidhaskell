module Goo where 

{-@ instance measure glub @-}
glub :: [Int] -> Bool
glub []     = True
glub (x:xs) = ((x > 0) && (glub xs))
