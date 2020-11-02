{-# LANGUAGE GADTs #-}
module T1777 where

-- Positive test cases for data constructor matching.

-- For attaching a termination measure, an empty datatype decl is ok.
--
-- In all other cases, we have to use the same constructors.

{-@

data D1 [len1]
data D2 = A2 Int | B2 Bool
data D3 [len3] = A3 Int | B3 Bool
data D4 where
  A4 :: Int -> D4
  B4 :: Bool -> D4

data D5 [len5] where
  A5 :: Int -> D5
  B5 :: Bool -> D5

measure len1
measure len3
measure len5

@-}

data D1 = A1 Int | B1 Bool
data D2 = A2 Int | B2 Bool
data D3 = A3 Int | B3 Bool

data D4 where
  A4 :: Int -> D4
  B4 :: Bool -> D4

data D5 where
  A5 :: Int -> D5
  B5 :: Bool -> D5

len1 :: D1 -> Int
len1 (A1 _) = 0
len1 (B1 _) = 0

len3 :: D3 -> Int
len3 (A3 _) = 0
len3 (B3 _) = 0

len5 :: D5 -> Int
len5 (A5 _) = 0
len5 (B5 _) = 0
