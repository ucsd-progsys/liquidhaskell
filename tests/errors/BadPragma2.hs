{-@ LIQUID "--expect-error-containing=Illegal pragma" @-}
{-@ LIQUID "--ghc-option=-O0" @-}

module BadPragma2 where

i :: Int
i = 1

