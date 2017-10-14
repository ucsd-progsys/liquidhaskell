{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--exactdc"        @-}

module ReflectLib7 where

{-@ reflect compose @-}
compose :: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)
