-- | Utilify functions for Diff static checks.
module LiftedFunctions where
 
-- | Measures for triplet projections.
{-@
measure fst3
measure snd3
measure thd3
@-}
fst3 :: (a, b, c) -> a
fst3 (x, _, _) = x
snd3 :: (a, b, c) -> b
snd3 (_, y, _) = y
thd3 :: (a, b, c) -> c
thd3 (_, _, z) = z
