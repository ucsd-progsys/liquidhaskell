module Goo where


{-@ foo :: x:_ -> {v:_ | fst v + snd v = x} @-}
foo :: Int -> (Int, Int)
foo x = (2, x-2)


{-@ test10 :: {v:_ | Prop v} @-}
test10     = x + y == 10
  where
    (x, y) = foo 10

-- THESE are also in GHC.Base.Spec
{-@ qualif Fst(v:a, y:b): v = fst y @-}
{-@ qualif Snd(v:a, y:b): v = snd y @-}


