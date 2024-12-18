{-@ LIQUID "--expect-error-containing=Unknown logic name `hi`" @-}
{-@ LIQUID "--expect-error-containing=Unknown logic name `wow`" @-}
{-@ LIQUID "--expect-error-containing=Unknown logic name `rubbish`" @-}
{-@ LIQUID "--expect-error-containing=Unknown logic name `this`" @-}
module UnboundFunInSpec2 where

{-@ foo :: Num a => { z : (xs:t -> {v : (t -> a) | this = rubbish }) | wow = hi } @-}
foo :: Num a => t -> t -> a
foo _ _ = 0
