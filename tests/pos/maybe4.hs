module Foo () where

{-@ goo   :: lo:{v0a: Maybe {v:a | ((isJust v0a) && (v = (fromJust v0a)))} | true } 
          -> hi:{v0b: Maybe {v:a | ((isJust v0b) && (v = (fromJust v0b)))} | (((isJust(lo) && isJust(v0b)) => (fromJust(v0b) >= fromJust(lo)))) }   
          -> Bool 
  @-}
goo       :: Maybe a -> Maybe a -> Bool
goo lo hi = bar (id hi) (id lo)

{-@ bar :: hi: Maybe a -> lo:Maybe {v: a | ((isJust(hi)) => (v <= fromJust(hi)))} -> Bool @-}
bar :: Maybe a -> Maybe a -> Bool
bar hi lo = True



