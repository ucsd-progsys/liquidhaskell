{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--rankNTypes" @-}
{-# LANGUAGE RankNTypes   #-}
module Test where


-- Needs rankNTypes flag: the function `first f` has ForallT type
-- so, it has no top refinements, so no way to get singleton type
-- rankNTypes flag makes a signleton syntactically, w/o need for refinements

{-@ sFF :: f:(a -> b) -> {o:SF a b | o == SF (first f) } @-}
sFF :: (a -> b) -> SF a b
sFF f = SF (first f)

data SF a b = SF (forall z. (a, z) -> (b,z))

{-@ reflect first @-}
first :: (a -> b) -> (forall z. (a,z) -> (b,z))
first f (a, z) = (f a, z)





