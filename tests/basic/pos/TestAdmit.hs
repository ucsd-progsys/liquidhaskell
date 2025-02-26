-- | Tests that Admit can be used to accept incomplete proofs
module TestAdmit where

import Language.Haskell.Liquid.ProofCombinators


{-@ g :: x:_ -> {v:_ | x == v} @-}
{-@ reflect g @-}
g :: Int -> Int
g x = x


{-@ f :: { g 1 == 1 } @-}
f :: ()
f = () *** Admit

