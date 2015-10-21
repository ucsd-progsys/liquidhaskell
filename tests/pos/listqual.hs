module ListQual () where

{-@ qualif OkAppend(v:List a, xs:List a, ys:List a): len v = len xs + len ys @-}

{-@ qualif BadAppend(v:[a], x:[a], ys:[a]): len v = len xs + len ys @-}

{- qualAppend :: xs:_ -> ys:_ -> {v:_ | len v = len xs + len ys} @-}
qualAppend :: [a] -> [a] -> [a]
qualAppend = undefined

append [] ys     = ys
append (x:xs) ys = x : append xs ys

{-@ boo :: {v:[Int] | len v = 2} @-}
boo :: [Int]
boo = append [1] [2]
