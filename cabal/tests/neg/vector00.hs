module Vec0 where

import LiquidPrelude

import Data.Vector

{-# ANN module "spec   $LIQUIDHS/Vector.spec" #-}
{-# ANN module "spec   $LIQUIDHS/List.spec" #-}
{-# ANN module "hquals $LIQUIDHS/List.hquals" #-}

xs    = [1,2,3,4] :: [Int]
vs    = fromList xs
jhala = vs ! 10
