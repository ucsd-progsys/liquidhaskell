module Goo where

{-@ foo :: Num a => { z : (xs:t -> {v : (t -> a) | this = rubbish }) | wow = hi } @-}
foo :: Num a => t -> t -> a
foo _ _ = 0
