module spec Data.Text.Lazy.Internal where


type NonEmptyStrict = {v:Data.Text.Internal.Text | (tlength v) > 0}

data Data.Text.Lazy.Internal.Text
    = Empty
    | Chunk (t :: NonEmptyStrict) (cs :: Data.Text.Lazy.Internal.Text)

measure ltlength :: Data.Text.Lazy.Internal.Text -> Integer
ltlength (Empty)      = 0
ltlength (Chunk t ts) = (tlength t) + (ltlength ts)

measure sum_ltlengths :: [Data.Text.Lazy.Internal.Text] -> Integer
sum_ltlengths ([]) = 0
sum_ltlengths (t:ts) = (ltlength t) + (sum_ltlengths ts)

invariant {v:Data.Text.Lazy.Internal.Text | (ltlength v) >= 0}
invariant {v:[Data.Text.Lazy.Internal.Text] | (sum_ltlengths v) >= 0}
invariant {v:[{v0:Data.Text.Lazy.Internal.Text | (sum_ltlengths v) >= (ltlength v0)}] | true}

chunk :: t:Data.Text.Internal.Text
      -> ts:Data.Text.Lazy.Internal.Text
      -> {v:Data.Text.Lazy.Internal.Text | ((ltlength v) = ((tlength t) + (ltlength ts)))}

empty :: {v:Data.Text.Lazy.Internal.Text | (ltlength v) = 0}

-- foldrChunks :: forall <p :: Data.Text.Lazy.Internal.Text -> a -> Prop>.
--                (   ts:Data.Text.Lazy.Internal.Text
--                 -> t:Data.Text.Internal.Text
--                 -> a<p ts>
--                 -> a<p (Data.Text.Lazy.Internal.Chunk t ts)>)
--             -> a<p Data.Text.Lazy.Internal.Empty>
--             -> t:Data.Text.Lazy.Internal.Text
--             -> a<p t>

-- foldlChunks :: forall <p :: Data.Text.Lazy.Internal.Text -> a -> Prop>.
--                cs:Data.Text.Lazy.Internal.Text
--             -> (   a<p cs>
--                 -> c:Data.Text.Internal.Text
--                 -> a<p cs>)
--             -> a<p cs>
--             -> t:Data.Text.Lazy.Internal.Text
--             -> a<p cs>

