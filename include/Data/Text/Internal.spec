module spec Data.Text.Internal where

predicate InBounds V H = ((H > 0) ? (Btwn V 0 H) : (V = 0))

data Data.Text.Internal.Text = Data.Text.Internal.Text
            (arr :: Data.Text.Array.Array)
            -- (off :: {v:Int | v >= 0})
            -- (len :: {v:Int | v >= 0})
            (off :: {v:Int | (((alen arr) > 0) ? (Btwn v 0 (alen arr)) : (v = 0))})
            (len :: {v:Int | (((alen arr) > 0) ? (BtwnI (v+off) off (alen arr)) : (v = 0))})

--             (off :: {v: Int | ((v >= 0) && (((alen arr) > 0) <=> (v < (alen arr))))})
--             (len :: {v: Int | ((v >= 0) && (((alen arr) > 0) <=> ((v+off) < (alen arr))))})
-- -- (len :: {v: Int | (v >= 0 && ((alen arr) = 0 || v = 0 || off < (alen arr)))})

measure tarr :: Data.Text.Internal.Text -> Data.Text.Array.Array
tarr (Data.Text.Internal.Text a o l) = a

measure toff :: Data.Text.Internal.Text -> Int
toff (Data.Text.Internal.Text a o l) = o

measure tlen :: Data.Text.Internal.Text -> Int
tlen (Data.Text.Internal.Text a o l) = l

measure sum_tlens :: [Data.Text.Internal.Text] -> Int
sum_tlens ([]) = 0
sum_tlens (t:ts) = (tlen t) + (sum_tlens ts)


measure numchars :: Data.Text.Array.Array -> Int -> Int -> Int

invariant {v:Data.Text.Internal.Text | (numchars (tarr v) (toff v) 0) = 0}
invariant {v:Data.Text.Internal.Text | (numchars (tarr v) (toff v) (tlen v)) >= 0}
invariant {v:Data.Text.Internal.Text | (numchars (tarr v) (toff v) (tlen v)) <= (tlen v)}

invariant {v:Data.Text.Internal.Text | (((tlength v) = 0) <=> ((tlen v) = 0))}
invariant {v:Data.Text.Internal.Text | (tlength v) >= 0}

measure tlength :: Data.Text.Internal.Text -> Int
tlength (Data.Text.Internal.Text a o l) = numchars(a,o,l)

measure sum_tlengths :: [Data.Text.Internal.Text] -> Int
sum_tlengths ([]) = 0
sum_tlengths (t:ts) = (tlength t) + (sum_tlengths ts)

text :: a:{v:Data.Text.Array.Array | (alen v) > 0}
     -> o:{v: Int | ((v >= 0) && (v < (alen a)))}
     -> l:{v: Int | ((v >= 0) && ((v+o) < (alen a)))}
     -> {v:Text | (((tarr v) = a) && ((toff v) = o) && ((tlen v) = l))}
-- text :: a:Data.Text.Array.Array
--      -> o:{v: Int | v >= 0}
--      -> l:{v: Int | v >= 0}
--      -> {v:Text | (((tarr v) = a) && ((toff v) = o) && ((tlen v) = l))}

empty :: {v:Data.Text.Internal.Text | (((tlen v) = 0) && ((tlength v) = 0))}

textP :: a:{v:Data.Text.Array.Array | (alen v) >= 0}
      -> o:{v:Int | (((alen a) > 0) ? (Btwn v 0 (alen a)) : (v = 0))}
      -> l:{v:Int | (((alen a) > 0) ? (Btwn (v+o) o (alen a)) : (v = 0))}
      -> {v:Data.Text.Internal.Text | (tlen v) = l}
-- textP :: a:Data.Text.Array.Array
--       -> o:{v:Int | v >= 0}
--       -> l:{v:Int | v >= 0}
--       -> {v:Data.Text.Internal.Text | (tlen v) = l}

