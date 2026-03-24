{-@ LIQUID "--expect-error-containing=Hole Found" @-}
{-@ LIQUID "--warn-on-term-holes" @-}

module Example1 where
    import Language.Haskell.Liquid.ProofCombinators (Proof)
    hole = undefined

    {-@ listLength :: xs:[a] -> {v : Nat | v == len xs} @-}
    listLength :: [a] -> Int
    listLength [] = 0
    listLength (_:xs) = 1 + listLength xs

    {-@ measure listLength @-}

    {-@ listLengthProof :: xs:[a] -> {listLength xs == len xs} @-}
    listLengthProof :: [a] -> Proof
    listLengthProof = hole
