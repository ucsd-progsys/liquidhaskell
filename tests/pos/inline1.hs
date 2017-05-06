module InlineMeasure where

data Zoo a = Z { elts :: [a], sz :: Int }

-- | this is not ok (unbound symbol `boo`)
{-@ data Zoo a = Z { elts :: [a], sz :: {v: Int | isBoo v elts} } @-}

{-@ inline isBoo @-}
isBoo :: Int -> [a] -> Bool
isBoo v e = v == boo e

{-@ type Moo a = {v:Zoo a | sz v = boo (elts v)} @-}

{-@ inline boo @-}
boo    :: [a] -> Int
boo xs = 0
