-- https://github.com/ucsd-progsys/liquidhaskell/issues/427

module Blank where

{-@ measure myprop @-} 
myprop :: Double -> Bool
myprop x = (fromIntegral (floor d) - d) == 0.0
  where d = (x / 3.0)

{-@ type Mytype = {v:Double | myprop v} @-}
type Mytype = Double

{-@ ok :: Mytype @-}
ok :: Mytype
ok = 6.0
