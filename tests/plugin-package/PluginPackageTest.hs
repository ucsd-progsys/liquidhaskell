-- | Test that LiquidHaskell works when loaded via -plugin-package
-- rather than -package. This verifies that LHAssumptions modules
-- are found through the plugin module search path.
module PluginPackageTest where

{-@ safeHead :: {v:[a] | len v > 0} -> a @-}
safeHead :: [a] -> a
safeHead (x:_) = x
safeHead []    = error "impossible"
