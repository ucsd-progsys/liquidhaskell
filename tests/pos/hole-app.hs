module Zoo where

{-@ type Vec a N = {v:[a] | len v = N } @-}

{-@ ok :: Vec Int 3 @-}
ok = [1,2,3] :: [Int]

{-@ ok' :: Vec _ 3 @-}  -- would be nice to support the hole in the application..
ok'     = [1,2,3]



