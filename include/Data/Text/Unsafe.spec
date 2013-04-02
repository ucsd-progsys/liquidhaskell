module spec Data.Text.Unsafe where

import Data.Text.Internal

predicate Btwn V X Y = ((X <= V) && (V < Y))
predicate BtwnEI V X Y = ((X < V) && (V <= Y))
predicate BtwnII V X Y = ((X <= V) && (V <= Y))

measure iter_i :: Iter -> Int
iter_i (Iter c i) = i

assume unsafeTail :: t:Text -> {v:Text | (tlength v) < (tlength t)}

assume iter_ :: t:Text -> i:{v:Int | (Btwn v 0 (tlen t))}
             -> {v:Int | ((BtwnEI (v+i) i (tlen t))
                      && ((numchars (tarr t) (toff t) (i+v)) 
                          = (1 + (numchars (tarr t) (toff t) i))))}

assume iter :: t:Text -> i:{v:Int | (Btwn v 0 (tlen t))}
            -> {v:Iter | ((BtwnEI ((iter_i v)+i) i (tlen t))
                     && ((numchars (tarr t) (toff t) (i+(iter_i v)))
                         = (1 + (numchars (tarr t) (toff t) i))))}
