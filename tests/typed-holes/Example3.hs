{-@ LIQUID "--expect-error-containing=Hole Found" @-}
{-@ LIQUID "--warn-on-term-holes" @-}
-- Based on paper: Theorem Proving for All: Equational Reasoning in Liquid Haskell (Functional Pearl)

module Example3 where
    import Prelude hiding ((<>), reverse, length, (++))
    import Language.Haskell.Liquid.ProofCombinators ((===), (***), QED(QED), Proof)

    hole = undefined

    {-@ length :: [a] -> {v:Int | 0 <= v } @-}
    length :: [a] -> Int
    length [] = 0
    length (_:xs) = 1 + length xs
    {-@ measure length @-}

    {-@ reverse :: is:[a] -> {os:[a] | length is == length os} @-}
    reverse :: [a] -> [a]
    reverse [] = []
    reverse (x:xs) = reverse xs ++ [x]

    {-@ (++) :: xs:[a] -> ys:[a] -> {zs:[a] | length zs == length xs + length ys} @-}
    (++) :: [a] -> [a] -> [a]
    [] ++ ys = ys
    (x:xs) ++ ys = x : (xs ++ ys)
    {-@ infixl ++ @-}

    {-@ reflect reverse @-}
    {-@ reflect ++ @-}


    --- Structural Induction will be needed. It could suggest as the next step.
    {-@ involutionProof :: xs:[a] -> { reverse (reverse xs) == xs } @-}
    involutionProof :: [a] -> Proof
    involutionProof xs = hole

    {-@ distributivityP :: xs:[a] -> ys:[a] -> { reverse (xs ++ ys) == reverse ys ++ reverse xs } @-}
    distributivityP :: [a] -> [a] -> Proof
    distributivityP xs ys = hole
