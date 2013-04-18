module spec Data.Text.Lazy.Internal where


type NonEmptyStrict = {v:Data.Text.Internal.Text | (tlength v) > 0}

data Data.Text.Lazy.Internal.Text
    = Empty
    | Chunk (t :: NonEmptyStrict) (cs :: Data.Text.Lazy.Internal.Text)

