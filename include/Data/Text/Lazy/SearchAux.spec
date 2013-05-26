module spec Data.Text.Lazy.SearchAux where

lackingHay :: q:{v:Int64 | v >= 0}
           -> t:NonEmptyStrict
           -> ts:Data.Text.Lazy.Internal.Text
           -> {v:Bool | ((Prop v) <=> (q > ((tlen t) + (ltlen ts))))}

buildTable :: Word16
           -> nlen:{v:Int64 | v > 1}
           -> ts0:{v:Data.Text.Lazy.Internal.Text | (BtwnI (ltlen v) 0 nlen)}
           -> t:{v:Data.Text.Internal.Text | (BtwnEI (tlen v) 0 nlen)}
           -> ts:{v:Data.Text.Lazy.Internal.Text |
                  (((ltlen v) + (tlen t)) = (nlen - (ltlen ts0)))}
           -> i:{v:Int | (Btwn v 0 (tlen t))}
           -> g:{v:Int64 | (BtwnI v 0 ((ltlen ts0) + i))}
           -> Word64
           -> {v:Int64 | (Btwn (v) (0) nlen)}
           -> PairS Word64 {v:Int64 | (Btwn (v) (0) nlen)}

