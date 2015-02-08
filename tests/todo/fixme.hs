module InlineMeasure where

data Zoo a = Z { elts :: [a], sz :: Int }

-- | this is not ok (unbound symbol `boo`)
{-@ data Zoo a = Z { elts :: [a], sz :: {v: Int | IsBoo v elts} } @-}

{-@ predicate IsBoo V E = V = boo E @-}
-- | this is ok

{-@ type Moo a = {v:Zoo a | sz v = boo (elts v)} @-}

{-@ inline boo @-}
boo    :: [a] -> Int
boo xs = 0
