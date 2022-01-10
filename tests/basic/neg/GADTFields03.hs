{-# LANGUAGE GADTs #-}

{-@ LIQUID "--exact-data-cons" @-}

-- With a refinement type embedded in a function using a fieldname, but with a
-- bad type

module GADTFields03 where

{-@
data T a where
  T :: { getT :: Int, getT' :: { v:Int | v >= 0 } } -> T Int 
 @-}
data T a where
  T :: { getT :: Int, getT' :: Int } -> T Int
  S :: { getT :: Int, getS :: String } -> T Int

{-@ f :: { v:T Int | getT' v < 0 } -> { x:Int | x >= 0 } @-}
f :: T Int -> Int
f = getT'

main :: IO ()
main = print (getT' (T 5 6))
