module spec Data.Text.Unsafe where

import Data.Text.Internal

predicate Btwn V X Y = ((X <= V) && (V < Y))
predicate BtwnEI V X Y = ((X < V) && (V <= Y))
predicate BtwnII V X Y = ((X <= V) && (V <= Y))

unsafeHead :: {v:Data.Text.Internal.Text | (tlength v) > 0}
           -> Char

unsafeTail :: t:{v:Data.Text.Internal.Text | (tlength v) > 0}
           -> {v:Data.Text.Internal.Text | (tlength v) = ((tlength t) - 1)}


iter_ :: t:Data.Text.Internal.Text
      -> i:{v:Int | (Btwn v 0 (tlen t))}
      -> {v:Int | (((BtwnEI (v+i) i (tlen t)))
                   && ((numchars (tarr t) (toff t) (i+v))
                           = (1 + (numchars (tarr t) (toff t) i)))
                        && ((numchars (tarr t) (toff t) (i+v))
                            <= (tlength t)))}
-- measure iter_d :: Data.Text.Unsafe.Iter -> Int
-- iter_d (Data.Text.Unsafe.Iter c d) = d


-- iter :: t:Data.Text.Internal.Text -> i:{v:Int | (Btwn v 0 (tlen t))}
--      -> {v:Data.Text.Unsafe.Iter | ((BtwnEI ((iter_d v)+i) i (tlen t))
--                                     && ((numchars (tarr t) (toff t) (i+(iter_d v)))
--                                         = (1 + (numchars (tarr t) (toff t) i)))
--                                     && ((numchars (tarr t) (toff t) (i+(iter_d v)))
--                                         <= (tlength t)))}


-- reverseIter :: t:Data.Text.Internal.Text
--             -> i:Int
--             -> l:{v:Int | (BtwnEI v 0 (tlen t))}
--             -> (Char,{v:Int | ((BtwnEI (l+v) 0 l)
--                                && ((numchars (tarr t) (toff t) (l+v))
--                                    = ((numchars (tarr t) (toff t) l) - 1))
--                                && ((numchars (tarr t) (toff t) (l+v))
--                                    >= 0))})

