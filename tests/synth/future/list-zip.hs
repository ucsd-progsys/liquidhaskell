{-@ LIQUID "--typed-holes" @-}

{-@ zip' :: xs: [a] -> {ys:[b] | len ys == len xs} -> {v:[(a, b)] | len v == len xs} @-}
zip' :: [a] -> [b] -> [(a, b)]
zip' = _zip'

-- zip' xs ys = 
--     case xs of
--         [] -> []
--         x3 : x4 ->
--             case ys of
--                 [] -> error "error"
--                 x7 : x8 -> (x3, x7) : (zip' x4 x8)

