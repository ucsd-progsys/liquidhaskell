-- We should reject the below to disallow uppercase binders

module NoUpperCaseBinders where

{-@ id :: foo: Int -> {v:Bool | v == foo}  @-}
id :: Int -> Int
id x = x
