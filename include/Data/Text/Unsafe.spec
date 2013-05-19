module spec Data.Text.Unsafe where

import Data.Text.Internal

unsafeHead :: {v:Data.Text.Internal.Text | (tlength v) > 0}
           -> Char

unsafeTail :: t:{v:Data.Text.Internal.Text | (tlength v) > 0}
           -> {v:Data.Text.Internal.Text | (tlength v) = ((tlength t) - 1)}


-- data Data.Text.Unsafe.Iter = Data.Text.Unsafe.Iter (c::Char) (i::Int)

-- measure iter_d :: Data.Text.Unsafe.Iter -> Int
-- iter_d (Data.Text.Unsafe.Iter c d) = d


-- iter :: t:Data.Text.Internal.Text -> i:{v:Int | (Btwn v 0 (tlen t))}
--      -> {v:Data.Text.Unsafe.Iter | ((BtwnEI ((iter_d v)+i) i (tlen t))
--                                     && ((numchars (tarr t) (toff t) (i+(iter_d v)))
--                                         = (1 + (numchars (tarr t) (toff t) i)))
--                                     && ((numchars (tarr t) (toff t) (i+(iter_d v)))
--                                         <= (tlength t)))}

iter_ :: t:Data.Text.Internal.Text
      -> i:{v:Int | (Btwn v 0 (tlen t))}
      -> {v:Int | (((BtwnEI (v+i) i (tlen t)))
                   && ((numchars (tarr t) (toff t) (i+v))
                       = (1 + (numchars (tarr t) (toff t) i)))
                   && ((numchars (tarr t) (toff t) (i+v))
                       <= (tlength t)))}

-- reverseIter :: t:Data.Text.Internal.Text
--             -> i:{v:Int | (Btwn v 0 (tlen t))}
--             -> l:{v:Int | (BtwnEI v 0 (tlen t))}
--             -> (Char,{v:Int | ((Btwn (l+v) 0 l)
--                                && ((numchars (tarr t) (toff t) (l+v))
--                                    = ((numchars (tarr t) (toff t) l) - 1))
--                                && ((numchars (tarr t) (toff t) (l+v))
--                                    >= -1))})


lengthWord16 :: t:Data.Text.Internal.Text
             -> {v:Int | v = (tlen t)}

takeWord16 :: k:Int
           -> {v:Data.Text.Internal.Text | (BtwnI k 0 (tlen v))}
           -> {v:Data.Text.Internal.Text | (tlen v) = k}

dropWord16 :: k:Int
           -> t:{v:Data.Text.Internal.Text | (BtwnI k 0 (tlen v))}
           -> {v:Data.Text.Internal.Text | (tlen v) = ((tlen t) - k)}
