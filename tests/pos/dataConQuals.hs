module Quals () where

data G = G { gx :: Int, gy :: Int }


-- | We should scrape qualifiers from data definitions; why doesn't it happen
--   "automatically" from the data-con-function signature anyway?

{-@ data G = G { gx :: Int, gy :: {v:Int | v = gx + 5} } @-}

poo :: Int -> Int
poo n = n + 5

-- | `goo` fails because `poo` doesn't have the type `n -> n + 5` because no qual...

{-@ goo :: {v:Int | v = 105} @-}
goo :: Int
goo = poo 100

-- | But `goo` succeeds if we add `chump` into the mix, because
--   it picks up the qualifers.

{- chump :: z:Int -> {v:Int | v = z + 5} @-}
chump   :: Int -> Int
chump z = z + 5

         
