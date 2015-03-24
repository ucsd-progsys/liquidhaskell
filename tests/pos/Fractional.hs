module Fixme where


{-@ foo :: Fractional a => {v:a | v >= 1.0} @-}
foo :: Fractional a => a
foo = undefined

{-@ foo'' :: RealFloat a => {v:a | v >= 1.0} @-}
foo'' :: RealFloat a => a
foo'' = undefined


{-@ foo' :: Num a => {v:a | v >= 1} @-}
foo' :: Num a => a
foo' = undefined