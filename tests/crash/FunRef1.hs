module Goo where

{-@ foo :: xs:_ -> {v:_ | this = rubbish } @-}
foo _ _ = 0
