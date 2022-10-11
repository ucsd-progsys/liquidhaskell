{-@ LIQUID "--expect-error-containing=Illegal type specification for `UnboundFunInSpec1.foo`" @-}
module UnboundFunInSpec1 where

{-@ foo :: xs:_ -> {v:_ | this = rubbish } @-}
foo _ _ = 0
