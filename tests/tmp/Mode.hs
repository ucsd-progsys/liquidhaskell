{-# LANGUAGE FlexibleInstances #-}

module Mode where

type Logical = Maybe Bool
type Numeric = Maybe Double

class Mode a
instance Mode Logical
instance Mode Numeric


class (Mode a) => IntoNumeric a where
  intoNumeric :: a -> Numeric

instance IntoNumeric Numeric where
  intoNumeric = id

instance IntoNumeric Logical where
  intoNumeric Nothing = Nothing
  intoNumeric (Just True)  = Just (1.0 :: Double)
  intoNumeric (Just False) = Just (0.0 :: Double)


class (Mode a) => IntoLogical a where
  intoLogical :: a -> Logical

instance IntoLogical Logical where
  intoLogical = id

instance IntoLogical Numeric where
  intoLogical Nothing    = Nothing
  intoLogical (Just 0.0) = Just False
  intoLogical (Just   _) = Just True


add :: (IntoNumeric a, IntoNumeric b) => a -> b -> Numeric
add l r = case (intoNumeric l, intoNumeric r) of
  ((Just l),(Just r)) -> Just (l + r)
  (       _,       _) -> Nothing

and :: (IntoLogical a, IntoLogical b) => a -> b -> Logical
and l r = case (intoLogical l, intoLogical r) of
  ((Just l),(Just r)) -> Just (l && r)
  (       _,       _) -> Nothing
