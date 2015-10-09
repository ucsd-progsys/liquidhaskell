module Zoo (test) where

inc :: Int -> Int 
inc x = x + 1

{-@ app :: _ -> Nat -> Nat @-} 
app :: (Int -> Int) -> Int -> Int
app f x = f x

test = app inc 7
