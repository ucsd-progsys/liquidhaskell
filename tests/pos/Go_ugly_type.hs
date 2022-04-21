module Go_ugly_type where

{- decrease go 2 @-}

{-@ rev :: xs:[a] -> {v: [a] | len v = len xs} @-}
rev = go [] 
  where 
    {-@ go :: acc:_ -> xs:_ -> {v:_ | len v = len acc + len xs} @-}
    go acc []     = acc
    go acc (x:xs) = go (x:acc) xs

main :: IO ()
main = pure ()
