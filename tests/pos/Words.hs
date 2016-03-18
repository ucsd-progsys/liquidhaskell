import Data.Word

{-@ foo :: {v:Word | v = 4} @-}
foo :: Word
foo = 4