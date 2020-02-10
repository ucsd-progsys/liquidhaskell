{-@ LIQUID "--typed-holes" @-}

module ListZip where 

{-@ zip' :: xs: [a] -> {ys:[b] | len ys == len xs} -> {v:[(a, b)] | len v == len xs} @-}
zip' :: [a] -> [b] -> [(a, b)]
zip' = _goal

