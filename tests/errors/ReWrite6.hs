{-@ LIQUID "--expect-error-containing=Unable to use ReWrite6.bad as a rewrite because it does not prove an equality" @-}
module ReWrite6 where

-- Reject non equalities
{-@ rewrite bad @-}
{-@ bad :: {1 < 2} @-}
bad :: ()
bad = ()
