module spec Data.Text.Lazy.Internal where


data Data.Text.Lazy.Internal.Text
    = Empty
    | Chunk (t :: NonEmptyStrict) (cs :: Data.Text.Lazy.Internal.Text)

measure ltlen :: Data.Text.Lazy.Internal.Text -> Integer
ltlen (Empty)      = 0
ltlen (Chunk t ts) = (tlen t) + (ltlen ts)

measure ltlength :: Data.Text.Lazy.Internal.Text -> Integer
ltlength (Empty)      = 0
ltlength (Chunk t ts) = (tlength t) + (ltlength ts)

measure sum_ltlengths :: [Data.Text.Lazy.Internal.Text] -> Integer
sum_ltlengths ([]) = 0
sum_ltlengths (t:ts) = (ltlength t) + (sum_ltlengths ts)

invariant {v:Data.Text.Lazy.Internal.Text | (ltlen v) >= 0}
invariant {v:Data.Text.Lazy.Internal.Text | (ltlength v) >= 0}
invariant {v:[Data.Text.Lazy.Internal.Text] | (sum_ltlengths v) >= 0}
invariant {v:[{v0:Data.Text.Lazy.Internal.Text | (sum_ltlengths v) >= (ltlength v0)}] | true}

chunk :: t:Data.Text.Internal.Text
      -> ts:Data.Text.Lazy.Internal.Text
      -> {v:Data.Text.Lazy.Internal.Text | ((ltlength v) = ((tlength t) + (ltlength ts)))}

empty :: {v:Data.Text.Lazy.Internal.Text | (ltlength v) = 0}

foldrChunks :: forall <p :: Data.Text.Lazy.Internal.Text -> a -> Prop>.
               (   ts:Data.Text.Lazy.Internal.Text
                -> t:NonEmptyStrict
                -> a<p ts>
                -> a<p (Data.Text.Lazy.Internal.Chunk t ts)>)
            -> a<p Data.Text.Lazy.Internal.Empty>
            -> t:Data.Text.Lazy.Internal.Text
            -> a<p t>

foldlChunks :: (a -> NonEmptyStrict -> a)
            -> a
            -> Data.Text.Lazy.Internal.Text
            -> a
