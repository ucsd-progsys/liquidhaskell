{-@ LIQUID "--expect-error-containing=Illegal pragma" @-}
{-@ LIQUID "--c-files=./wow.c" @-}

module BadPragma1 where

i :: Int
i = 1

