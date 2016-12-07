module Class3 where

{-@ class Pos s where
      allPos :: x:s Int -> {v:Bool | Prop v <=> allPos x}
  @-}
class Pos s where
  allPos :: s Int -> Bool

instance Pos [] where
  {-@ instance measure allPos :: [Int] -> Bool
        allPos []     = (0 < 1)
        allPos (x:xs) = (0 < 1)
    @-}
  allPos []     = True
  allPos (x:xs) = (x > 0) && (allPos xs)
