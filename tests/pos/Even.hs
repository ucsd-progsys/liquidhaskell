module Even where 

{-@ type Even = {v:Int | v mod 2 = 0} @-}

{-@ notEven :: Int -> Even @-}
notEven :: Int -> Int
notEven x = x * 2
