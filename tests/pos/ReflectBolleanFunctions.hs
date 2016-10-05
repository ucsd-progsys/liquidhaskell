{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exactdc" @-}
{-@ LIQUID "--higherorder"        @-}
module Data.Foo where


{-@ reflect foo @-}
foo :: (Int -> Bool) -> (Int -> Bool) -> Bool 
foo f g = (f 1) && (g 1)