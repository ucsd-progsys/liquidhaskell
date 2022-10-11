{-@ LIQUID "--reflection" @-}

module T819 where

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding ((<>))

data L a = N 
{-@ infixl 9 <> @-}


{-@ foo :: xs:L a -> {xs <> N == N } @-}
foo :: L a -> Proof
foo N = N <> N === N *** QED 


{-@ reflect <> @-}
(<>) :: L a -> L a -> L a 
N <> N = N 


{-@ infixl 9 +++ @-}
{-@ data N = Zero | Succ {next :: N} @-}
data N = Zero | Succ N 

{-@ reflect +++ @-}
(+++) :: N -> N -> N
n +++ m = n

{-@ lemma :: { v:() | Zero +++ Zero == Zero } @-}
lemma :: ()
lemma = Zero +++ Zero === Zero *** QED

