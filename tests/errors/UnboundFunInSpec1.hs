module UnboundFunInSpec1 where

{-@ foo :: xs:_ -> {v:_ | this = rubbish } @-}
foo _ _ = 0
