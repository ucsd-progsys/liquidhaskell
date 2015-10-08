module Test1 () where

inc :: Int -> Int
inc x = x + 1

test1 :: Int -> Int
test1 n = let b = 0 <= n in
          if b then
            let a = inc n
            in
               div n a
          else
            1
