{-@ 
    zipWith :: f: (a -> b -> c) 
               -> xs: [a] 
               -> { ys: [b] | len ys == len xs} 
               -> {v: [c] | len v == len xs } 
@-}
zipWith :: (a -> b -> c) -> [a] -> [b] -> [c]
zipWith = _zipWith


-- zipWith f xs ys =
--      case xs of
--          [] -> []
--          x3 : x4 ->
--              case ys of
--                  [] -> error "error"
--                  x7 : x8 -> (f x3 x7) : (zipWith f x4 x8)