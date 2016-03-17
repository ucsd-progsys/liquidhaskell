module T602 where

{-@
class Num a => Foo a where
    foo :: { x : a | x /= 0 } -> {v:a | v > 0}
@-}

class Num a => Foo a where
    foo :: a -> a

-- instance Foo Double where
--     foo = id

instance Foo Int where
    foo x = 0

-- example :: (Num a, Foo a) => a
-- example :: Double

example :: Int
example = foo 0
