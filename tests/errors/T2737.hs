{-@ LIQUID "--expect-error-containing=PLE is not enabled for `prop`" @-}
{-@ LIQUID "--reflection" @-}

-- Neither --ple-local nor --ple is set, so the annotation below has nothing to
-- act on.
module T2737 where

{-@ reflect double @-}
double :: Int -> Int
double x = x + x

{-@ automatic-instances prop @-}
{-@ prop :: {v:() | double 2 == 4} @-}
prop :: ()
prop = ()
