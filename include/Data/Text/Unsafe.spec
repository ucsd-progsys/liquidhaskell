module spec Data.Text.Unsafe where

import Data.Text.Internal

predicate Btwn V X Y = ((X <= V) && (V < Y))
predicate BtwnI V X Y = ((X <= V) && (V <= Y))

assume unsafeTail :: t:Text -> {v:Text | (tlen v) < (tlen t)}

assume iter_ :: t:Text -> i:{v:Int | (Btwn v 0 (tlen t))}
             -> {v:Int | ((BtwnI (v+i) i (tlen t)) 
                      && ((numchars (tarr t) (toff t) (i+v)) 
                          = (1 + (numchars (tarr t) (toff t) i))))}
