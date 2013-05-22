module spec Data.Text.Lazy.Search where

-- FIXME: Prove this
indices :: pat:Data.Text.Lazy.Internal.Text
        -> src:Data.Text.Lazy.Internal.Text
        -> [{v:Int64 | (BtwnI v 0 ((ltlen src) - (ltlen pat)))}]<{\ix iy ->
                         (ix+(ltlen pat)) <= iy}>
