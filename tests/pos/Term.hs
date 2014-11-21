module Term where



{-@ f :: _ -> xs : [a] -> [a] / [len xs] @-}
f er [] = error er
f er (x:xs) = (x+1) : f er xs

{-@ f' :: _ -> xs : [a] -> [a] / [len xs] @-}
f' er [] = error er
f' er (x:xs) = x : f' er xs

{-@ type ListN a N = {v:[a] | len v = N} @-}
{-@ type ListL a L = ListN a (len L) @-}

{-@ safeZipWithError :: _ -> xs:[a] -> ListL b xs -> ListL (a,b) xs / [len xs] @-}
safeZipWithError msg (x:xs) (y:ys) = (x,y) : safeZipWithError msg xs ys
safeZipWithError _   []     []     = []
safeZipWithError msg _      _      = error msg
