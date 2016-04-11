-- #658, fails if you comment out test1 (and test2?)

{-@ test1 :: n: {v : Int | v >= 0} -> lst: {v : [a] | n < len v} -> {v : [a] | len v = len lst - n } @-}
test1 :: Int -> [a] -> [a]
test1 n lst = b where (_, b) = splitAt n lst

{-@ test2 :: n: {v : Int | v >= 0} -> lst: {v : [a] | n < len v} -> {v : [a] | len v = n } @-}
test2 :: Int -> [a] -> [a]
test2 n lst = a where (a, _) = splitAt n lst

{-@ test3 :: n: {v : Int | v >= 0} -> lst: {v : [a] | n < len v} -> {v : [a] | len v = len lst } @-}
test3 :: Int -> [a] -> [a]
test3 n lst = a ++ b where (a, b) = splitAt n lst
