{-@ assume foo :: x:{Int|x /= 0} -> {v:Int|v == 5} @-}
{-@ foo :: x:{Int|x /= 0} -> {v:Int|v = 5 / x} @-}
foo :: Int -> Int
foo = div 5

{-@ bar :: {v:Int|v == 5} @-}
bar :: Int
bar = foo 4