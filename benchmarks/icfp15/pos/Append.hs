{-@ LIQUID "--no-termination" @-}

module Compose where

import Prelude hiding ((++))
{-@ type OList a = [a]<{\x v -> v >= x}> @-}

{-@ (++) :: forall <p :: a -> Bool, q :: a -> Bool, w :: a -> a -> Bool>.
        {x::a<p> |- a<q> <: a<w x>}
        [a<p>]<w> -> [a<q>]<w> -> [a]<w> @-}
(++) []      ys = ys
(++) (x:xs) ys = x:(xs ++ ys)

{-@ qsort :: xs:[a] -> OList a  @-}
qsort []     = []
qsort (x:xs) = (qsort [y | y <- xs, y < x]) ++ (x:(qsort [z | z <- xs, z >= x]))
