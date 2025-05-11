{-@ LIQUID "--expect-error-containing=Hole Found" @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--warn-on-term-holes" @-}
-- Based on paper: Theorem Proving for All: Equational Reasoning in Liquid Haskell (Functional Pearl)

module Example5 where
    import Prelude hiding ((<>), reverse, length, (++))
    import Language.Haskell.Liquid.ProofCombinators ((===), (***), (?), QED(QED), Proof)

    hole = undefined

    data Tree = Leaf Int | Node Tree Tree

    {-@ reflect flatten @-}
    flatten :: Tree -> [Int]
    flatten (Leaf x) = [x]
    flatten (Node l r) = flatten l ++ flatten r


    {-@ length :: [a] -> {v:Int | 0 <= v } @-}
    length :: [a] -> Int
    length [] = 0
    length (_:xs) = 1 + length xs
    {-@ measure length @-}

    {-@ (++) :: xs:[a] -> ys:[a] -> {zs:[a] | length zs == length xs + length ys} @-}
    (++) :: [a] -> [a] -> [a]
    [] ++ ys = ys
    (x:xs) ++ ys = x : (xs ++ ys)
    {-@ infixl ++ @-}
    {-@ reflect ++ @-}
    

    {-@ flattenApp :: t:Tree -> ns:[Int] -> { v:[Int] | v == flatten t ++ ns } @-}
    flattenApp :: Tree -> [Int] -> [Int]
    flattenApp t ns = hole -- Structural Induction
