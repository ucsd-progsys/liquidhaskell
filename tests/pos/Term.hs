{-@ LIQUID "--no-totality"    @-}

module Term where

import Language.Haskell.Liquid.Prelude (unsafeError)

-- TODO: If we remove the type signature LH crashes
f :: (Num a) => String -> [a] -> [a]
{-@ f :: _ -> xs : [a] -> [a] / [len xs] @-}
f er [] = unsafeError er
f er (x:xs) = (x+1) : f er xs

f' :: String -> [a] -> [a]
{-@ f' :: _ -> xs : [a] -> [a] / [len xs] @-}
f' er [] = unsafeError er
f' er (x:xs) = x : f' er xs

{-@ type ListN a N = {v:[a] | len v = N} @-}
{-@ type ListL a L = ListN a (len L) @-}

safeZipWithError :: String -> [a] -> [b] -> [(a, b)]
{-@ safeZipWithError :: _ -> xs:[a] -> ListL b xs -> ListL (a,b) xs / [len xs] @-}
safeZipWithError msg (x:xs) (y:ys) = (x,y) : safeZipWithError msg xs ys
safeZipWithError _   []     []     = []
safeZipWithError msg _      _      = unsafeError msg
