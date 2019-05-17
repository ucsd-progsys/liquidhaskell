{-@ greater :: { k:Int | k > 1 } -> i:Int -> { j:Int | j - k > 0 } @-}
greater :: Int -> Int -> Int 
greater = _greater