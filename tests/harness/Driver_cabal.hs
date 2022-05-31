-- | Test driver for cabal-based builds.

import Test.Build
import Test.Options
import Options.Applicative

main :: IO ()
main = simpleProgram cabalTestEnv cabalRun =<< execParser opts
