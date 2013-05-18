module spec Data.Text.Search where

-- FIXME: Prove this
indices :: pat:Data.Text.Internal.Text
        -> src:Data.Text.Internal.Text
        -> [{v:Int | (Btwn v 0 ((tlen src) - (tlen pat)))}]<{\ix iy ->
                       (ix+(tlen src)) <= iy}>

