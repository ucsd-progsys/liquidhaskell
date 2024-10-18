{-# Language GADTs #-}

{-@ LIQUID "--ple"           @-}
{-@ LIQUID "--reflection"    @-}
{-@ LIQUID "--etabeta"       @-}
{-@ LIQUID "--dependantcase" @-}

module ProposalLocalRewrites where

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (id)

{-@ reflect id @-}
id :: Int -> Int
id x = x

data Term where
    {-@ MkId :: Prop (Term id) @-}
    MkId :: Term
data TERM = Term (Int -> Int)

{-@ doSomething :: f:_ -> Prop (Term f) -> {f = id} @-}
doSomething :: (Int -> Int) -> Term -> Proof
doSomething _ MkId = trivial

{-@ doSomething' :: f:_ -> Prop (Term f) -> {f 42 = 42} @-}
doSomething' :: (Int -> Int) -> Term -> Proof
doSomething' _ MkId = trivial