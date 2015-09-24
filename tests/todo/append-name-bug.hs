-- | BUG: prop_app_nil_ok works fine, but prop_app_nil_bad doesn't.
--   The only difference is the type of axiom_append_nil_{bad, ok},
--   in which the only difference is that one uses the {...N...} while
--   the other does not. For some reason this yields two DIFFERENT refinements,
--   one with Append.N and one with N, which causes the problem.

{-@ LIQUID "--no-termination"  @-}

module Append where

data L a = N |  C a (L a) deriving (Eq)

{-@ N :: {v:L a | v == N }                       @-}
{-@ C :: x:a -> xs:L a -> {v:L a | v == C x xs } @-}

{-@ measure append :: L a -> L a -> L a @-}
{-@ assume append :: xs:L a -> ys:L a -> {v:L a | v == append xs ys } @-}

append :: L a -> L a -> L a
append N xs        = xs
append (C y ys) xs = C y (append ys xs)

{-@ assume axiom_append_nil_bad :: xs:L a -> Equal {append N xs} xs @-}
axiom_append_nil_bad :: L a -> Proof
axiom_append_nil_bad xs = Proof

{-@ assume axiom_append_nil_ok :: xs:L a -> {v:Proof | (append N xs) == xs} @-}
axiom_append_nil_ok :: L a -> Proof
axiom_append_nil_ok xs = Proof

data Proof = Proof

{-@ invariant {v:Proof | v == Proof }   @-}

{-@ type Equal X Y = {v:Proof | X == Y} @-}

{-@ prop_app_nil_ok :: ys:L a -> {v:Proof | append N N == N } @-}
prop_app_nil_ok N = axiom_append_nil_ok N

{-@ prop_app_nil_bad :: ys:L a -> {v:Proof | append N N == N } @-}
prop_app_nil_bad N = axiom_append_nil_bad N
