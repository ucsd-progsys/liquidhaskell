module Fixme where
{-@ LIQUID "--no-termination" @-}
{-@ type SL a = [a]<{\x v -> x <= v}> @-}

import State

foo :: Int -> State a Int
foo y = return y
