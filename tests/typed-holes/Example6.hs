{-@ LIQUID "--expect-error-containing=Hole Found" @-}
{-@ LIQUID "--warn-on-term-holes" @-}
-- Based on paper: Theorem Proving for All: Equational Reasoning in Liquid Haskell (Functional Pearl)
{-@ infix    :   @-}

module Example6 where
    import Prelude hiding ((<>), reverse, length, (++))
    import Language.Haskell.Liquid.ProofCombinators ((===), (***), (?), QED(QED), Proof)
    hole = undefined
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


    data Expr = Val Int |  Add Expr Expr

    {-@ reflect eval @-}
    eval :: Expr -> Int
    eval (Val n) = n
    eval (Add e1 e2) = eval e1 + eval e2

    type Stack = [Int]
    type Code  = [Op]
    data Op  = PUSH Int | ADD

    {-@ reflect exec @-}
    exec :: Code -> Stack -> Maybe Stack
    exec []           s = Just s
    exec (PUSH n : c) s = exec c (n:s)
    exec (ADD : c)    (m:n:s) = exec c (m+n:s)
    exec _ _            = Nothing

    {-@ reflect comp @-}
    comp :: Expr -> Code
    comp (Val n) = [PUSH n]
    comp (Add x y) = comp x ++ comp y ++ [ADD]

    {-@ generalizedCorrectness 
         :: e:Expr -> s:Stack -> {exec (comp e) s == Just ((eval  e):s) } 
    @-}
    generalizedCorrectness :: Expr -> Stack -> Proof
    generalizedCorrectness e s = hole -- Structural Induction
