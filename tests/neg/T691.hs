-- We should reject the below to disallow uppercase binders

module NoUpperCaseBinders where

{-@ id :: Foo:Int -> Int  @-}
id :: Int -> Int
id x = x
