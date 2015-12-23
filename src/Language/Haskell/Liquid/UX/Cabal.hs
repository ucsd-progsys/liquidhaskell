module Language.Haskell.Liquid.UX.Cabal (withCabal) where

-- withCabal :: Config -> IO Config
withCabal :: a -> IO a
withCabal = return


{-

DEPRECATED: use `stack exec -- liquid /path/to/file.hs` for now

import Language.Fixpoint.Misc (traceShow)
import Language.Haskell.Liquid.UX.Errors
import Language.Haskell.Liquid.UX.Config (Config (..))
import qualified Language.Haskell.GhcOpts as GhcOpts
import Data.List  (isPrefixOf, nub)
import Data.Maybe (mapMaybe)


---------------------------------------------------------------------------------------
withCabal :: Config -> IO Config
---------------------------------------------------------------------------------------
withCabal cfg
  | cabalDir cfg = either abort (reconfig cfg) <$> GhcOpts.ghcOpts tgt
  | otherwise    = return cfg
  where
    tgt          = target cfg

abort :: String -> a
abort = exitWithPanic . ("Cannot get GHC flags: " ++)

target :: Config -> FilePath
target cfg = case files cfg of
               f:_ -> f
               _   -> exitWithPanic "Please provide a single verification target."

reconfig :: Config -> GhcOpts.Config -> Config
reconfig cfg c = cfg { idirs      = traceShow "Opts-Dirs: " dirs
                     , ghcOptions = traceShow "Opts-Opts: " opts
                     }
  where
    opts       = ghcOptions cfg  ++ fs
    dirs       = nub $ idirs cfg ++ includeDirs fs
    fs         = GhcOpts.configGhcOpts c

includeDirs :: [String] -> [FilePath]
includeDirs = mapMaybe isInclude

isInclude :: String -> Maybe String
isInclude f
  | "-i/" `isPrefixOf` f = Just $ drop 2 f
  | otherwise            = Nothing

-}
