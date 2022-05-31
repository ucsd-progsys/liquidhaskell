-- Fails because we cannot catch parse errors with --expect-error-containing
{-@ LIQUID "--expect-error-containing=Cannot parse specification" @-}
-- We should reject the below to disallow uppercase binders

module ParseBind where

{-@ id :: Foo:Int -> Int  @-}
id :: Int -> Int
id x = x
