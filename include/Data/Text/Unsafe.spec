module spec Data.Text.Unsafe where

import Data.Text.Internal

predicate Btwn V X Y = ((X <= V) && (V < Y))
predicate BtwnEI V X Y = ((X < V) && (V <= Y))
predicate BtwnII V X Y = ((X <= V) && (V <= Y))


assume unsafeTail :: t:Text -> {v:Text | (tlength v) < (tlength t)}


assume iter_ :: t:Text -> i:{v:Int | (Btwn v 0 (tlen t))}
             -> {v:Int | (((BtwnEI (v+i) i (tlen t)))
                          && ((numchars (tarr t) (toff t) (i+v))
                                  = (1 + (numchars (tarr t) (toff t) i)))
                          && ((numchars (tarr t) (toff t) (i+v))
                                 <= (tlength t)))}
