module Foo () where

-- -> hi  : {v: Maybe {v: a | ( isJust(hi0) && (v = fromJust(hi0)) && ((isJust(lo)) => (v >= fromJust(lo))))} | v = hi0 }   

{-@ foo :: lo0 : Maybe a
        -> lo  : {v: Maybe {v: a | (isJust(lo0) && (v = fromJust(lo0))) } | v = lo0 }  
        -> hi0 : Maybe a
        -> hi  : {v: Maybe {v: a | ( isJust(hi0) && (v = fromJust(hi0))) } 
                   | (((isJust(lo) && isJust(v)) => (fromJust(v) >= fromJust(lo))) && (v = hi0)) }   
        -> Bool @-}
foo :: Maybe a -> Maybe a -> Maybe a -> Maybe a -> Bool
foo lo0 lo hi0 hi = bar (id hi) (id lo)



{-@ bar :: hi: Maybe a 
        -> lo:Maybe {v: a | ((isJust(hi)) => (v <= fromJust(hi))) }  
        -> Bool @-}
bar :: Maybe a -> Maybe a -> Bool
bar hi lo = True



