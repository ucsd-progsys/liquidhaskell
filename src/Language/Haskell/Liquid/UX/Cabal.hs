module Language.Haskell.Liquid.UX.Cabal (withCabal) where

import Language.Haskell.Liquid.UX.Errors
import Language.Haskell.Liquid.UX.Config (Config (..))
import Language.Haskell.GhcOpts (ghcOpts)
import System.Console.CmdArgs.Explicit
import System.Console.CmdArgs.Implicit     hiding (Loud)
import System.Console.CmdArgs.Text
import qualified GHC
import Data.List  (isPrefixOf, nub)
import Data.Maybe (mapMaybe)

---------------------------------------------------------------------------------------
withCabal :: Config -> IO Config
---------------------------------------------------------------------------------------
withCabal cfg
  | cabalDir cfg = either abort (reconfig cfg) <$> ghcOpts tgt
  | otherwise    = return cfg
  where
    tgt          = target cfg

-- whenLoud $ putStrLn $ "addCabalDirs: " ++ tgt

abort :: String -> a
abort = exitWithPanic . ("Cannot get GHC flags: " ++)

target :: Config -> FilePath
target cfg = case files cfg of
               f:_ -> f
               _   -> exitWithPanic "Please provide a single verification target."

reconfig :: Config -> [String] -> Config
reconfig cfg fs = cfg { idirs      = nub $ idirs cfg ++ includeDirs fs
                      , ghcOptions =       ghcOptions cfg ++ fs
                      }

includeDirs :: [String] -> [FilePath]
includeDirs = mapMaybe isInclude

isInclude :: String -> Maybe String
isInclude f
  | "-i/" `isPrefixOf` f = Just $ drop 2 f
  | otherwise            = Nothing

{-
GHC OPTS : ["-O0"]GHC OPTS :
["-w","-v0"
 ,"-fbuilding-cabal-package"
 ,"-O"
 ,"-outputdir"
 ,".stack-work/dist/x86_64-osx/Cabal-1.22.4.0/build"
 ,"-odir",".stack-work/dist/x86_64-osx/Cabal-1.22.4.0/build","-hidir",".stack-work/dist/x86_64-osx/Cabal-1.22.4.0/build","-stubdir",".stack-work/dist/x86_64-osx/Cabal-1.22.4.0/build","-i","-i/Users/rjhala/research/stack/liquid/liquidhaskell/./src","-i/Users/rjhala/research/stack/liquid/liquidhaskell/./include","-i/Users/rjhala/research/stack/liquid/liquidhaskell/./.","-i/Users/rjhala/research/stack/liquid/liquidhaskell/./.stack-work/dist/x86_64-osx/Cabal-1.22.4.0/build","-i/Users/rjhala/research/stack/liquid/liquidhaskell/./tests","-i/Users/rjhala/research/stack/liquid/liquidhaskell/./.stack-work/dist/x86_64-osx/Cabal-1.22.4.0/build/autogen","-I.stack-work/dist/x86_64-osx/Cabal-1.22.4.0/build/autogen","-I.stack-work/dist/x86_64-osx/Cabal-1.22.4.0/build","-optP-include","-optP.stack-work/dist/x86_64-osx/Cabal-1.22.4.0/build/autogen/cabal_macros.h","-hide-all-packages","-no-user-package-db","-package-db","/Applications/ghc-7.10.2.app/Contents/lib/ghc-7.10.2/package.conf.d","-package-db","/Users/rjhala/.stack/snapshots/x86_64-osx/nightly-2015-09-24/7.10.2/pkgdb","-package-db","/Users/rjhala/research/stack/liquid/liquidhaskell/.stack-work/install/x86_64-osx/nightly-2015-09-24/7.10.2/pkgdb","-package-id","Cabal-1.22.4.0-43515548ac8e8e693b550dcfa1b04e2b","-package-id","Diff-0.3.2-d60e738085e24bd2ba085853867b84a6","-package-id","aeson-0.9.0.1-ea82995047cb231c94231aee293436ee","-package-id","array-0.5.1.0-d4206b835b96b5079d918fa1eab1a9a8","-package-id","bifunctors-5-9497b78c1808987b8601618de2742b5c","-package-id","cpphs-1.19.3-21d69634848f44bbddd2385456c13030","-package-id","fingertree-0.1.1.0-e8cb817ba02a5ed615b3a46f18f3fd8f","-package-id","ghc-paths-0.1.0.9-b18f6718b3226041485a4e0a0842c180","-package-id","hashable-1.2.3.3-09c4177c49dd46a63f7036317bb17114","-package-id","hpc-0.6.0.2-49bce407db3f37807645ac03c42b8ff3","-package-id","hscolour-1.23-77c6937e0747fc7892d42aa452545b51","-package-id","parsec-3.1.9-bddea73c8bf2d5ff1335dae2cc92e789","-package-id","syb-0.5.1-09089498a055bd723b4a95c1351d3c8a","-package-id","template-haskell-2.10.0.0-161ca39a5ae657ff216d049e722e60ea","-package-id","text-1.2.1.3-2395ef415c1b20175aae83b50060e389","-package-id","time-1.5.0.1-710377a9566ae0edafdde8dc74a184c3","-package-id","vector-0.10.12.3-67219b7cb09d19688dca52e92595a7d6","-package-id","bytestring-0.10.6.0-6e8453cb70b477776f26900f41a5e17a","-package-id","cereal-0.4.1.1-e7af0306d1317407815a09e40431fc3f","-package-id","cmdargs-0.10.13-a8aec3840014c1a2b642b8ee0671d451","-package-id","daemons-0.2.1-0b0661a02074f525101355cceebca33b","-package-id","data-default-0.5.3-a2ece8050e447d921b001e26e14476f2","-package-id","deepseq-1.4.1.1-5de90d6c626db2476788444fb08c1eb3","-package-id","ghc-7.10.2-5c2381785a7b22838c6eda985bc898cf","-package-id","liquid-fixpoint-0.6-f8a9eb45028ec5187b4eaaaab5a1396e","-package-id","network-2.6.2.1-54f9bbbc4dc78b945fb82127414a5b82","-package-id","pretty-1.1.2.0-1d31b75e6aa28069010db3db8ab24535","-package-id","prover-0.1.0.0-af42484d037d94d0e2b5c21591019282","-package-id","unix-2.7.1.0-75051e1ddce506fe76a9ea932b926357","-package-id","unordered-containers-0.2.5.1-09ed02f61ed89449c8cd4b51d7f295c2","-package-id","base-4.8.1.0-075aa0db10075facc5aaa59a7991ca2f","-package-id","containers-0.5.6.2-2b49cce16f8a2908df8454387e550b93","-package-id","directory-1.2.2.0-16f6a661d4e92cd8da4d681a1d197064","-package-id","filepath-1.4.0.0-8fee9c13b5e42926cc01f6aa7c403c4b","-package-id","mtl-2.2.1-5cf332b11edb88a6040af20fd6a58acb","-package-id","optparse-applicative-0.11.0.2-64c4a013db45b66a7b578a0a518d7f3d","-package-id","process-1.2.3.0-36e5501145ab363f58c5e5a7079e9636","-package-id","stm-2.4.4-2526ff89874f899372b2e4f544bb03cd","-package-id","tagged-0.8.1-8fb7724b78ef88e44ca8950c77a173f6","-package-id","tasty-0.10.1.2-3edf1ce479f2dc1472803ce20060e1e3","-package-id","tasty-hunit-0.9.2-dc3e487b6addcc5acb2e3cf6fcd6ae50","-package-id","tasty-rerun-1.1.5-69a2e8be39919b24c991bdcc6778a213","-package-id","transformers-0.4.2.0-21dcbf13c43f5d8cf6a1f54dee6c5bff","-XHaskell98","-XPatternGuards","-W","-fno-warn-unused-imports","-fno-warn-dodgy-imports","-fno-warn-deprecated-flags","-fno-warn-deprecations","-fno-warn-missing-methods","-O2","-threaded","-O0"]
rjhala@borscht ~/r/s/l/liquidhaskell (lhi)> cd src/ rjhala@borscht ~/r/s/l/l/src
(lhi)> ack "updateDynFlags" Language/Haskell/Liquid/GhcInterface.hs


-}
