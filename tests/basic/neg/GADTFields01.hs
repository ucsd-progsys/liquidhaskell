{-# LANGUAGE GADTs #-}

-- With a refinement type embedded in a function using a fieldname, but with a
-- bad type

module GADTFields01 where

{-@
data T where
  T :: { getT :: Int, getT' :: Int } -> T 
 @-}
data T where
  T :: { getT :: Int, getT' :: Int } -> T

{-@ f :: { v:T | getT' v < 0 } -> { x:Int | x >= 0 } @-}
f :: T -> Int
f = getT'

main :: IO ()
main = print (getT' (T 5 6))
