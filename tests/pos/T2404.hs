module T2404 where


{-@ lists :: (l::Int, {v:[Char] | len v = l}, {v:[Int] | len v = l}) @-}
lists :: (Int, [Char], [Int])
lists = (3, "abc", [7, 8, 9])