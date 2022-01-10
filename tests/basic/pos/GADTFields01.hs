{-# LANGUAGE GADTs #-}

-- With a refinement type embedded

module GADTFields01 where

{-@
data T where
  T :: { getT :: Int, getT' :: { v:Int | v >= 0 } } -> T
 @-}
data T where
  T :: { getT :: Int, getT' :: Int } -> T

main :: IO ()
main = print ()
