module TheSizeOfStructures where

import Prelude hiding (map)

-- | Does list map Terminate?

infixr `C`
data List a = N | C a (List a)

lmap              :: (a -> b) -> (List a) -> (List b)
lmap _ N          = N
lmap f (x `C` xs) = f x `C` lmap f xs


-- | Express Termination Metric

{-@ measure llen  :: (List a) -> Int
    llen (N)      = 0
    llen (C x xs) = 1 + (llen xs)
  @-}

{-@ invariant {v:(List a) | (llen v) >= 0}@-}


-- | Relate List with its length

{-@ data List [llen] @-}


-- | Choosing the correct argument

{-@ Decrease posSum 2 @-}
posSum                            :: Int -> (List Int) -> Int
posSum acc N                      = acc
posSum acc (x `C` xs) | x > 0     = posSum (acc + x) xs
                      | otherwise = posSum (acc)     xs

-- | Standard lists

{- 
 measure len :: [a] -> Int
 len ([])   = 1
 len (x:xs) = 1 + (len xs)
-} 

map          :: (a -> b) -> [a] -> [b]
map _ []     = []
map f (x:xs) = f x : map f xs
