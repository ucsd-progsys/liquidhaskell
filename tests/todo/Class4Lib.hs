module Class4Lib where

{-@ class Pos s where
      allPos :: s a -> Bool
  @-}
class Pos s where
  allPos :: s a -> Bool
