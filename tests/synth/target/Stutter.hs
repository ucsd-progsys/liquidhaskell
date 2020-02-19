{-@ LIQUID "--typed-holes" @-}

{-@ err :: { v: Int | false } -> a @-}
err :: Int -> a
err s = undefined


{-@ stutter :: xs:[a] -> {v:[a] | 2 * len xs ==  len v} @-}
stutter :: [a] -> [a]
stutter = _x

-- stutter []     = []
-- stutter (x:xs) = x:x:stutter xs
