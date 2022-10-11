{-@ LIQUID "--expect-error-containing=Illegal pragma" @-}
{-@ LIQUID "--idirs=.." @-}

module BadPragma0 where

i :: Int
i = 1

