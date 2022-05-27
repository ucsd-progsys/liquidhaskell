module IncrLib (incr) where 


{-@ axiomatize incr @-}
incr :: Int -> Int
incr x = x + 1
