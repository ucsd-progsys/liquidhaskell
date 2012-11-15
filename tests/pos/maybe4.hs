module Foo where

-- -> hi  : {v: Maybe {v: a | ( isJust(hi0) && (v = fromJust(hi0)) && ((isJust(lo)) => (v >= fromJust(lo))))} | v = hi0 }   


{-@ goo   :: lo  : {v0: Maybe {v:a  | (isJust(v0) && (v = fromJust(v0)))}  
          -> hi  : {v0: Maybe {v: a | ( isJust(v0) && (v = fromJust(v0)))} | (((isJust(lo) && isJust(v0)) => (fromJust(v0) >= fromJust(lo)))) }   
          -> Bool @-}
goo       :: Maybe a -> Maybe a -> Bool
goo lo hi = bar (id hi) (id lo)

{-@ bar :: hi: Maybe a -> lo:Maybe {v: a | ((isJust(hi)) => (v <= fromJust(hi)))} -> Bool @-}
bar :: Maybe a -> Maybe a -> Bool
bar hi lo = True



