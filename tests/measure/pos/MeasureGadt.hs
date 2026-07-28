{-# LANGUAGE GADTs #-}
{-# LANGUAGE MonoLocalBinds #-}
module MeasureGadt where

-- | A measure over a GADT whose constructor has a concrete (non-vanilla)
-- result type. The constructor @C :: T ()@ has a worker type of the form
-- @forall a. (a ~ ()) => T a@, i.e. it carries an equality coercion argument.
-- LiquidHaskell must still attach the measure equation to the worker data
-- constructor so that pattern matching on @C@ learns @m v = 0@.
data T a where
  C :: T ()

{-@ measure m @-}
{-@ m :: T a -> Int @-}
m :: T a -> Int
m C = 0

{-@ go :: v : T a -> { n : Int | n = m v } @-}
go :: T a -> Int
go C = 0
