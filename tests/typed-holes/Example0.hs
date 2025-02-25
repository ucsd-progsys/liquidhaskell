{-@ LIQUID "--expect-error-containing=Hole Found" @-}
{-@ LIQUID "--warn-on-term-holes" @-}

module Example0 where
    hole = undefined

    {-@ listLength :: xs:[a] -> {v : Nat | v == len xs} @-}
    listLength :: [a] -> Int
    listLength [] = hole
    listLength (_:xs) = 1 + listLength xs
