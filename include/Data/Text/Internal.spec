module spec Data.Text.Internal where

textP :: A.Array -> Int -> len:Int -> {v:Text | ((tlen v) = len)}
