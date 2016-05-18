-- #658, fails if you comment out test1 (and test2?)

{-@ test3 :: n:Nat -> lst:{ [a] | n < len lst} -> {v : [a] | len v = len lst } @-}
test3 :: Int -> [a] -> [a]
test3 n lst = a ++ b where (a, b) = splitAt n lst
