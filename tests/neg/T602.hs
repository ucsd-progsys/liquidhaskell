module T602 where

-- UNSOUNDLY SAFE
{-@
class Fractional a => Foo a where
    foo :: { x : a | x /= 0.0 } -> a
@-}

-- UNSAFE
{-
class Fractional a => Foo a where
    foo :: { x : a | x /= 0.0 } -> a
@-}

class Fractional a => Foo a where
    foo :: a -> a

instance Foo Double where
    foo = id

example :: Double
example = foo 0.0
