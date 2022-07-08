{-# LANGUAGE GADTs #-}

{-@ LIQUID "--exact-data-cons" @-}

-- With a refinement type embedded and then used wrongly

module GADTFields00 where

{-@
data T where
  T :: { getT :: Int, getT' :: { v:Int | v >= 0 } } -> T
 @-}
data T where
  T :: { getT :: Int, getT' :: Int } -> T

{-@ f :: T -> { v:Int | v < 0} @-}
f :: T -> Int
f = getT'

main :: IO ()
main = print (getT' (T 5 6))
