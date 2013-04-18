module spec Data.Text.Internal where

data Data.Text.Internal.Text = Data.Text.Internal.Text
            (arr :: Data.Text.Array.Array)
            (off :: {v: Int | v >= 0 })
            (len :: {v: Int | v >= 0 })
-- (len :: {v: Int | (v >= 0 && ((alen arr) = 0 || v = 0 || off < (alen arr)))})

measure tarr :: Data.Text.Internal.Text -> Data.Text.Array.Array
tarr (Data.Text.Internal.Text a o l) = a

measure toff :: Data.Text.Internal.Text -> Int
toff (Data.Text.Internal.Text a o l) = o

measure tlen :: Data.Text.Internal.Text -> Int
tlen (Data.Text.Internal.Text a o l) = l

measure numchars :: Data.Text.Array.Array -> Int -> Int -> Int

invariant {v:Data.Text.Internal.Text | (numchars (tarr v) (toff v) 0) = 0}
invariant {v:Data.Text.Internal.Text | (numchars (tarr v) (toff v) (tlen v)) >= 0}
invariant {v:Data.Text.Internal.Text | (numchars (tarr v) (toff v) (tlen v)) <= (tlen v)}

invariant {v:Data.Text.Internal.Text | (((tlength v) = 0) <=> ((tlen v) = 0))}
invariant {v:Data.Text.Internal.Text | (tlength v) >= 0}

measure tlength :: Data.Text.Internal.Text -> Int
tlength (Data.Text.Internal.Text a o l) = numchars(a,o,l)

textP :: Data.Text.Array.Array
      -> Int
      -> len:Int
      -> {v:Data.Text.Internal.Text | ((tlen v) = len)}
empty :: {v:Data.Text.Internal.Text | (((tlen v) = 0) && ((tlength v) = 0))}
