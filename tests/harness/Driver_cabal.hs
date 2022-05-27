-- | Test driver for cabal-based builds.

import Test.Build
import Test.Options
import Options.Applicative

main :: IO ()
main = program cabalTestEnv cabalOutputStripper cabalErrorStripper cabalBuild =<< execParser opts
