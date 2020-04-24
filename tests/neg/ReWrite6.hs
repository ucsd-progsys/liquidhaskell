module ReWrite6 where

-- Reject non equalities
{-@ rewrite bad @-}
{-@ bad :: {1 < 2} @-}
bad :: ()
bad = ()
