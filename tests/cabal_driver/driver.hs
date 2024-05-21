-- | Test driver for cabal-based builds.

import Test.Build
import Test.Options

main :: IO ()
main = program cabalTestEnv cabalRun =<< parseOptions
