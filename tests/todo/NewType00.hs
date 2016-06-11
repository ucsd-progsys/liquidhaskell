module NT where

{- newtype Natural = Natural { toInt :: Nat } @-}
newtype Natural = Natural { toInt :: Int }

foo :: Int -> Maybe Natural
foo n
  | 0 <= n    = Just (Natural n)
  | otherwise = Nothing

{-@ bar :: Natural -> Nat @-}
bar (Natural n) = n
