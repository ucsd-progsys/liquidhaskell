{-@ LIQUID "--higherorder"     @-}
{- LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}
{-@ LIQUID "--fuel=10" @-}

{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts #-}
module ListFunctors where

import MaybeReflect1
import Prelude hiding (Maybe(..))
import Language.Haskell.Liquid.ProofCombinators


-- This is OK

{-@ compositionOK :: x:Maybe (a -> a)
                -> y:Maybe (a -> a)
                -> z:Maybe a
                -> { seqm x (seqm y z)  = seqm x (seqm y z) } @-}

compositionOK :: Maybe (a -> a) -> Maybe (a -> a) -> Maybe a -> Proof
compositionOK = undefined 



-- But the following says "unbound symbol seqm"
-- Which is weird as seqm is OK in the above signature

{-


 /Users/niki/liquidtypes/liquidhaskell/tests/todo/ApplicativeMaybe1.hs:28:20: Error: Bad Type Specification
 ListFunctors.composition :: x:(Maybe (a -> a)) -> y:(Maybe (a -> a)) -> z:(Maybe a) -> {VV : () | seqm (seqm (seqm (purem composem) x) y) z == seqm x (seqm y z)}
     Sort Error in Refinement: {VV : Tuple | seqm (seqm (seqm (purem composem) x) y) z == seqm x (seqm y z)}
     Unbound Symbol seqm
 Perhaps you meant: head, len, snd

-}

{-@ composition :: x:Maybe (a -> a)
                -> y:Maybe (a -> a)
                -> z:Maybe a
                -> { (seqm (seqm (seqm (purem composem) x) y) z)  = seqm x (seqm y z) } @-}

composition :: Maybe (a -> a) -> Maybe (a -> a) -> Maybe a -> Proof
composition = undefined 







