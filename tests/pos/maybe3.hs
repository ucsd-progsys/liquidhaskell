module Foo () where


{-@ foo :: lo0 : Maybe a
        -> lo  : {v: Maybe {v: a | mbIsJust lo0 && v = mbFromJust lo0 } | v = lo0 }  
        -> hi0 : Maybe a
        -> hi  : {v: Maybe {v: a | mbIsJust hi0 && v = mbFromJust hi0 } 
                   | (((mbIsJust lo && mbIsJust v) => (mbFromJust v >= mbFromJust lo)) && (v = hi0)) }   
        -> Bool @-}
foo :: Maybe a -> Maybe a -> Maybe a -> Maybe a -> Bool
foo lo0 lo hi0 hi = bar (id hi) (id lo)

{-@ bar :: hi: Maybe a 
        -> lo:Maybe {v: a | ((mbIsJust hi) => (v <= mbFromJust hi)) }  
        -> Bool @-}
bar :: Maybe a -> Maybe a -> Bool
bar hi lo = True



