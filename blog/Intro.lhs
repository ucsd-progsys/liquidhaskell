Refinement Types 101
====================

\begin{code}
module Intro where
\end{code}

One of the great things about Haskell, is its brainy type system that
allows us to enforce a variety of invariants at compile time, and hence
precluding a large swathe of errors at run time.

What is a Refinement Type?
--------------------------

Refinement types allow us to enrich types with *logical predicates* which
allow us to specify even more sophisticated properties. Rather than beating
about the bush, let us jump right in and see what refinement types look like!

Consider, if you will, the number `3`.
