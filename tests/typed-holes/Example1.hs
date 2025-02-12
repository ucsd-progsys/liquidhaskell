{-@ LIQUID "--expect-error-containing=Hole Found" @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--allow-typed-holes" @-}
-- Based on https://ucsd-progsys.github.io/liquidhaskell-blog/2016/10/06/structural-induction.lhs/

module Example1 where
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