{-@ LIQUID "--expect-error-containing=Unknown logic name `rubbish`" @-}
{-@ LIQUID "--expect-error-containing=Unknown logic name `this`" @-}
module UnboundFunInSpec1 where

{-@ foo :: xs:_ -> {v:_ | this = rubbish } @-}
foo _ _ = 0
