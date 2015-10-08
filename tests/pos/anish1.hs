module Test1 () where

inc :: Int -> Int
inc xoooo = xoooo + 1

test1 :: Int -> Int
test1 nine = let b = 0 <= nine in
          if b then
            let a = inc nine
            in
               div nine a
          else
            1
