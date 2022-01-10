{-# LANGUAGE GADTs #-}

-- Basic syntax checking

module GADTFields00 where

{-@
data T where
  T :: { getT :: Int } -> T
 @-}
data T where
  T :: { getT :: Int } -> T

main :: IO ()
main = print ()
