module BadParse where


{-@ test :: v:a -> (r:a, l:a) @-}
test x = (x, x)
