{-@ LIQUID "--expect-error-containing=Illegal type specification for `UnboundFunInSpec2.foo`" @-}
module UnboundFunInSpec2 where

{-@ foo :: Num a => { z : (xs:t -> {v : (t -> a) | this = rubbish }) | wow = hi } @-}
foo :: Num a => t -> t -> a
foo _ _ = 0
