module NewType3 where

newtype    Wrap a = Wrap {unwrap :: a }
{-@ newtype Wrap a = Wrap {unwrap :: a } @-}

{-@ wrapTheorem :: x:Wrap a -> {x == Wrap (unwrap x)} @-}
wrapTheorem :: Wrap a -> ()
wrapTheorem (Wrap _) = ()

