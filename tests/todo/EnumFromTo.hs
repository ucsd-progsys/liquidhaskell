module Foo where

new :: l -> [i] -> [sd] -> ([i], [(Int, sd)])
new l wids m | not (null wids) && length m <= length wids && not (null m)
  = (unseen, visi)
  where (seen,unseen) = splitAt (length m) wids
        (cur:visi)    = [ (s, sd) |  (s, sd) <- zip [0..(length m) ] m ]
                -- now zip up visibles with their screen id
new _ _ _ = error "non-positive argument to StackSet.new"

foo :: Num a => a -> [a]
foo = undefined
{-@ assume foo :: Num a => x:a -> {v:[a] | (len v) = x} @-}
