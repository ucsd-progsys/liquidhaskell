module Risers  where

{-@ LIQUID "--totality" @-}

{-@ predicate NonNull X = ((len X) > 0) @-}

{- risers :: (Ord a) => zs:[a] -> {v: [[a]] | ((NonNull zs) => (NonNull v)) } @-} 
risers []        
  = []
risers [x]       
  = [[x]]
risers (x:y:etc) 
  = if x <= y then (x:s):ss else [x]:(s:ss)
    where (s:ss) = risers [] -- insert partiality (y:etc)
