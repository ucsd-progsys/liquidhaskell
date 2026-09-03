-- | Regression test: pattern matching on the tuple result of an `ignore`d
-- binding used to panic with "safeBkArrow on RAllP". The scrutinee's type is
-- built directly from the GHC type (so it lacks the abstract-refinement
-- argument that the tuple constructor's dependent-pair encoding expects), and
-- LiquidHaskell now defaults the leftover abstract refinement to `True`.
--
-- See 'Language.Haskell.Liquid.Constraint.Generate.defaultPvs'.
module IgnoreTupleAbsRef where

{-@ ignore bar @-}
bar :: Int -> (Int, Maybe Int)
bar n = (n, Nothing)

foo :: Int -> Int
foo x = case bar x of
          (n, _) -> n
