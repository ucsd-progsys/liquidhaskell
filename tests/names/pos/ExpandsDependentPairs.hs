-- | Tests that Id is correctly expanded. Before fixing, this test would
-- fail with
--
-- > lookupTyThing: cannot resolve a LHRLogic name "Id"
--
module ExpandsDependentPairs where

{-@ type Id = {v:Int | v >= 0} @-}

{-@ lemma :: l:Id -> (id::Id, { true }) @-}
lemma :: Int -> (Int, ())
lemma x = (x, ())
