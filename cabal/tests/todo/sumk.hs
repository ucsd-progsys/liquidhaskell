module Test0 where

import LiquidPrelude

{-# ANN module "hquals sumk.hs.hquals" #-}

m   = choose 0
bot = choose 0

dsum ranjit jhala k =
  if (ranjit `leq` 0)
    then k jhala 
    else dsum (ranjit `minus` 1) (ranjit `plus` jhala) k

prop0 = dsum m bot (\x -> assert ((m `plus` bot) `leq` x))

