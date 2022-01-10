{-# LANGUAGE GADTs #-}

{-@ LIQUID "--exact-data-cons" @-}

-- With shared field names

module GADTFields04 where

{-@
data T a where
  T :: { getT :: Int, getT' :: { v:Int | v >= 0 } } -> T Int
  S :: { getT :: Int, getS :: String } -> T Int
 @-}
data T a where
  T :: { getT :: Int, getT' :: Int } -> T Int
  S :: { getT :: Int, getS :: String } -> T Int

{-@ f :: { v:T Int | getT v >= 0 } -> { x: Int | x >= 0 } @-}
f :: T Int -> Int
f = getT

main :: IO ()
main = do
  print (f (T 5 6))
  print (f (S 3 ""))
