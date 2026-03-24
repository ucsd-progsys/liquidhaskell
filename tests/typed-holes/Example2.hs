{-@ LIQUID "--expect-error-containing=Hole Found" @-}
{-@ LIQUID "--warn-on-term-holes" @-}
-- Based on https://ucsd-progsys.github.io/liquidhaskell-blog/2016/10/06/structural-induction.lhs/

module Example2 where
    import Prelude hiding ((<>))
    import Language.Haskell.Liquid.ProofCombinators ((===), (***), QED(QED), Proof)

    hole = undefined

    {-@ reflect empty @-}
    empty  :: [a]
    empty  = []

    {-@ infix <> @-}
    {-@ reflect <> @-}
    (<>) :: [a] -> [a] -> [a]
    [] <> xs = xs
    (x:xs) <> ys = x : (xs <> ys)

    {-@ leftId  :: x:[a] -> { (empty <> x) == x } @-}
    leftId :: [a] -> Proof
    leftId x
        =   empty <> x
        === hole
        === x
        *** QED

    {-@ rightId  :: x:[a] -> { (x <> empty) == x } @-}
    rightId :: [a] -> Proof
    rightId x = hole

    {-@ assoc  :: x:[a] -> y:[a] -> z:[a] -> { (x <> (y <> z)) == ((x <> y) <> z) } @-}
    assoc :: [a] -> [a] -> [a] -> Proof
    assoc x y z = hole
