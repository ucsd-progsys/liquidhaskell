{-@ LIQUID "--no-termination" @-}

module RecNonFunc where

{-@ reflect eq @-}
{-@ eq :: xs:[Int] -> {ys:[Int]|len xs = len ys} -> Bool @-}
eq :: [Int] -> [Int] -> Bool
eq [] [] = True
eq (x:xs) (y:ys) = if x == y then eq xs ys else False

r :: [Int]
r = let cons = (:) in 0 `cons` r

{-@ relational r ~ r :: [Int] ~ [Int] 
                     ~~ RecNonFunc.eq r1 r2 @-}

r' :: Bool
r' = if True then False else r'
