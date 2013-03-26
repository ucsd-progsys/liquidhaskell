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

invariant {v:Text | (numchars (tarr v) (toff v) 0) = 0}
invariant {v:Text | (numchars (tarr v) (toff v) (tlen v)) <= (tlen v)}

-- measure tlength :: Text -> Int
-- tlength (Text a o l) = numchars(a,o,l)

textP :: A.Array -> Int -> len:Int -> {v:Text | ((tlen v) = len)}
empty :: {v:Text | (((tlen v) = 0) && ((numchars (tarr v) (toff v) (tlen v)) = 0))}
