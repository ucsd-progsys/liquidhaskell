{-@ LIQUID "--typed-holes" @-}

module UniqueListRange where

{-@ zero :: { v: Int | v == 0} @-}
zero :: Int
zero = 0

{-@ inc :: x: Int -> { v: Int | v == x + 1} @-}
inc :: Int -> Int
inc x = x + 1

{-@ dec :: x: Int -> { v: Int | v == x - 1} @-}
dec :: Int -> Int
dec x = x - 1

{-@ leq :: x: Int -> y: Int -> { v: Bool | v <=> (x <= y) } @-}
leq :: Int -> Int -> Bool
leq x y = x <= y

{-@ range :: size: Nat -> lo: Int -> { v: [ { v: Int | lo <= v && v <= lo + size} ] | len v == size } 
  @-}
range :: Int -> Int -> [Int]
range size lo =
    case leq size zero of
        True  -> [ ]
        False -> lo : (range (dec size) (inc lo))
