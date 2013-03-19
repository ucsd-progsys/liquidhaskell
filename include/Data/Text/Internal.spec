module spec Data.Text.Internal where

data Text = Text
            (arr :: A.Array)
            (off :: {v: Int | v >= 0 })
            (len :: {v: Int | v >= 0 })
-- (len :: {v: Int | (v >= 0 && ((alen arr) = 0 || v = 0 || off < (alen arr)))})

measure tarr :: Text -> A.Array
tarr (Text a o l) = a

measure toff :: Text -> Int
toff (Text a o l) = o

measure tlen :: Text -> Int
tlen (Text a o l) = l

measure numchars :: A.Array -> Int -> Int -> Int
-- numchars a o 0 = 0

textP :: A.Array -> Int -> len:Int -> {v:Text | ((tlen v) = len)}
empty :: {v:Text | (tlen v) = 0}
