-- | Correctness of sat solver as in Trellys
-- | http://www.seas.upenn.edu/~sweirich/papers/popl14-trellys.pdf

module Solver where

import Data.Tuple
import Language.Haskell.Liquid.Prelude ((==>))

-- | Formula
type Var     = Int
data Lit     = Pos Var | Neg Var
type Clause  = [Lit]
type Formula = [Clause]

-- | Assignment

type Asgn = [(Var, Bool)]

-- | Top-level "solver"


{-@ solve :: f:_ -> Maybe {a:Asgn | Prop (sat a f) } @-}
solve   :: Formula -> Maybe Asgn
solve f = find (\a -> sat a f) (asgns f)

{-@ bound witness @-}
witness :: Eq a => (a -> Bool) -> (a -> Bool -> Bool) -> a -> Bool -> a -> Bool
witness p w = \ y b v -> b ==> w y b ==> (v == y) ==> p v

{-@ find :: forall <p :: a -> Prop, w :: a -> Bool -> Prop>.
            (Witness a p w) =>
            (x:a -> Bool<w x>) -> [a] -> Maybe (a<p>) @-}
find :: (a -> Bool) -> [a] -> Maybe a
find f [] = Nothing
find f (x:xs) | f x       = Just x
              | otherwise = Nothing

-- | Generate all assignments

asgns :: Formula -> [Asgn] -- generates all possible T/F vectors
asgns = undefined

{-@ axiomatize sat @-}
sat :: Asgn -> Formula -> Bool
sat _ _ = True
