module Foo where

-- -> hi  : {v: Maybe {v: a | ( isJust(hi0) && (v = fromJust(hi0)) && ((isJust(lo)) => (v >= fromJust(lo))))} | v = hi0 }   


{-@ goo   :: lo  : Maybe {v:a | (isJust(lo) && (v = fromJust(lo)))}  
          -> hi  : {v: Maybe {v: a | ( isJust(hi) && (v = fromJust(hi)))} 
                     | (((isJust(lo) && isJust(v)) => (fromJust(v) >= fromJust(lo)))) }   
          -> Bool @-}
goo       :: Maybe a -> Maybe a -> Bool
goo lo hi = bar (id hi) (id lo)

{-@ bar :: hi: Maybe a 
        -> lo:Maybe {v: a | ((isJust(hi)) => (v <= fromJust(hi))) }  
        -> Bool @-}
bar :: Maybe a -> Maybe a -> Bool
bar hi lo = True



