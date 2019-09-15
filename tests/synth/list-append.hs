{-@ LIQUID "--typed-holes" @-}

{-@ append :: xs: [a] -> ys: [a] -> {v:[a] | len v == len xs + len ys} @-}
append :: [a] -> [a] -> [a]
append = _append

-- append xs ys =
--  case ys of
--      [] -> xs
--      x3 : x4 ->
--          case xs of
--              [] -> ys
--              x7 : x8 -> x3 : (append x8 ys)