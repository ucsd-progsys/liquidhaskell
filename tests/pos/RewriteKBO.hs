module RewriteKBO where

{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--fast" @-}
{-@ LIQUID "--rw-termination-check" @-}
{-@ LIQUID "--rest-ordering=kbo" @-}

import Language.Haskell.Liquid.ProofCombinators

data Set = Empty | Tree Int Set Set

{-@ infix \/ @-}
{-@ measure \/ :: Set -> Set -> Set @-}
{-@ assume \/ :: a : Set -> b : Set -> { v : Set | v = a \/ b } @-}
(\/) :: Set -> Set -> Set
a \/ b = undefined


{-@ infix /\ @-}
{-@ measure /\ :: Set -> Set -> Set @-}
{-@ assume /\ :: a : Set -> b : Set -> { v : Set | v = a /\ b } @-}
(/\) :: Set -> Set -> Set
a /\ b = undefined

{-@ measure emptySet :: Set @-}
{-@ assume emptySet :: {v : Set | v = emptySet} @-}
emptySet :: Set
emptySet = undefined

{-@ predicate IsSubset M1 M2 = M1 \/ M2 = M2 @-}
{-@ predicate IsDisjoint M1 M2 = M1 /\ M2 = emptySet @-}

{-@ rewrite unionIntersect @-}
{-@ assume unionIntersect :: s0 : Set -> s1 : Set -> s2 : Set -> { (s0 \/ s1) /\ s2 = (s0 /\ s2) \/ (s1 /\ s2) } @-}
unionIntersect :: Set -> Set -> Set -> Proof
unionIntersect _ _ _ = ()

{-@ rewrite intersectSelf @-}
{-@ assume intersectSelf :: s0 : Set -> { s0 /\ s0 = s0 } @-}
intersectSelf :: Set -> Proof
intersectSelf _ = ()

{-@ rewrite unionIdemp @-}
{-@ assume unionIdemp :: ma : Set -> {v : () | IsSubset ma ma } @-}
unionIdemp :: Set -> Proof
unionIdemp _ = ()

{-@ rewrite unionAssoc @-}
{-@ assume unionAssoc :: ma : Set -> mb : Set -> mc : Set -> {v : () | (ma \/ mb) \/ mc = ma \/ (mb \/ mc) } @-}
unionAssoc :: Set  -> Set  -> Set  -> Proof
unionAssoc _ _ _ = ()

{-@ rewrite unionComm @-}
{-@ assume unionComm :: ma : Set -> mb : Set -> {v : () | ma \/ mb = mb \/ ma } @-}
unionComm :: Set  -> Set  -> Proof
unionComm _ _ = ()

{-@ rewrite intersectComm @-}
{-@ assume intersectComm :: ma : Set -> mb : Set -> {v : () | ma /\ mb = mb /\ ma } @-}
intersectComm :: Set  -> Set -> Proof
intersectComm _ _ = ()

{-@ rewrite unionEmpty @-}
{-@ assume unionEmpty :: ma : Set -> {v : () | ma \/ emptySet = ma } @-}
unionEmpty :: Set -> Proof
unionEmpty _ = ()

{-======================================================
              Proofs
=======================================================-}

{-@ unionMono :: s : Set -> s2 : Set -> {s1 : Set | IsSubset s1 s2 } -> { IsSubset (s \/ s1) (s \/ s2)} @-}
unionMono :: Set -> Set -> Set -> Proof
unionMono s s2 s1 = ()
