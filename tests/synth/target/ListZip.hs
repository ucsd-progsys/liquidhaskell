{-@ LIQUID "--typed-holes" @-}

module ListZip where 

{-@ zip' :: xs: [a] -> {ys:[b] | len ys == len xs} -> {v:[(a, b)] | len v == len xs} @-}
zip' :: [a] -> [b] -> [(a, b)]
zip' = _goal

-- zip' xs ys = 
--     case xs of 
--         []     ->   case ys of
--                         []      -> []
--                         (x1:x2) -> error " len mismatch "
--         x0:xs0 ->   case ys of
--                         [] -> error " len mismatch "
--                         (y0:ys0) -> (x0, y0) : zip' xs0 ys0
