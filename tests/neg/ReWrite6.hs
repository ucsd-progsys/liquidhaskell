module ReWrite6 where

{-@ rewrite bad @-}
{-@ bad :: {1 < 2} @-}
bad :: ()
bad = ()
