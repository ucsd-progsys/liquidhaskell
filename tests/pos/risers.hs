module Risers () where

{-@ predicate NonNull X = ((len X) > 0) @-}

{-@ risers :: (Ord a) => zs:[a] -> {v: [[a]] | ((NonNull zs) => (NonNull v)) } @-} 
risers []        
  = []
risers [x]       
  = [[x]]
risers (x:y:etc) 
  = if x <= y then (x:s):ss else [x]:(s:ss)
    where (s, ss) = safeSnoc $ risers (y:etc)

{-@ safeSnoc     :: {v : [a] | (NonNull v) } -> (a, [a]) @-}
safeSnoc (x:xs)  = (x, xs)
safeSnoc _       = error "WHOOPS!"
