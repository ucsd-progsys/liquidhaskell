module Loop (listSum) where

{-@ LIQUID "--no-termination"@-}

-- listSum     :: [Int] -> Int
-- listNatSum  :: [Int] -> Int
-- listEvenSum :: [Int] -> Int
-- add         :: Int -> Int -> Int

loop :: Int -> Int -> a -> (Int -> a -> a) -> a
loop lo hi base f = go lo base
  where 
    go i acc 
      | i < hi    = go (i+1) (f i acc)
      | otherwise = acc
      
listSum xs  = loop 0 n 0 body 
  where 
    body    = \i acc -> acc + (xs !! i) -- replace !! with `poo` and its safe? wtf.
    n       = length xs
