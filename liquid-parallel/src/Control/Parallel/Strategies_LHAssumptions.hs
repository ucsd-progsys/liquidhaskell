{-# OPTIONS_GHC -Wno-unused-imports #-}
module Control.Parallel.Strategies_LHAssumptions where

import Control.Parallel.Strategies

{-@
assume Control.Parallel.Strategies.withStrategy :: Control.Parallel.Strategies.Strategy a -> x:a -> {v:a | v == x}
@-}
