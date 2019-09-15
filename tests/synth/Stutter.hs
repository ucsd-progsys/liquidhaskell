{-@ LIQUID "--typed-holes" @-}



{-@ stutter :: xs:[a] -> {v:[a] | 2 * len xs ==  len v} @-}
stutter :: [a] -> [a]
stutter = _stutter

-- stutter []     = []
-- stutter (x:xs) = x:x:stutter xs
