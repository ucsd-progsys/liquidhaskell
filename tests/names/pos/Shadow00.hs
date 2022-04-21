-- TAG: resolve 
-- this tests whether we can resolve the name 'even' to the local definition, 
-- and not 'GHC.Real.even'

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Shadow00 where

import qualified Prelude

data Peano = O | S Peano

data BBool = BTrue | BFalse

{-@ reflect negb @-}
negb :: BBool -> BBool
negb BTrue  = BFalse
negb BFalse = BTrue

{-@ reflect even @-}
even :: Peano -> BBool
even O         = BTrue
even (S O)     = BFalse
even (S (S n)) = even n

{-@ thmEvenS :: n:Peano -> { even (S n) == negb (even n) } @-}
thmEvenS :: Peano -> () 
thmEvenS O         = () 
thmEvenS (S O)     = () 
thmEvenS (S (S n)) = thmEvenS n
