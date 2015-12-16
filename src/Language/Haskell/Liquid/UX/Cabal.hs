module Language.Haskell.Liquid.UX.Cabal (withCabal) where

import Language.Haskell.Liquid.UX.Errors
import Language.Haskell.Liquid.UX.Config (Config (..))
import Language.Haskell.GhcOpts (ghcFlags)
import System.Console.CmdArgs.Explicit
import System.Console.CmdArgs.Implicit     hiding (Loud)
import System.Console.CmdArgs.Text
import qualified GHC

---------------------------------------------------------------------------------------
withCabal :: Config -> IO Config
---------------------------------------------------------------------------------------
withCabal cfg
  | cabalDir cfg = withCabal' cfg
  | otherwise    = return cfg

withCabal' cfg = do
  whenLoud $ putStrLn $ "addCabalDirs: " ++ tgt
  io <- ghcFlags tgt
  case io of
    Left e -> exitWithPanic $ "Cannot get GHC flags: " ++ e
    Just i  -> return $ fixCabalDirs' cfg i
  where
    tgt = case files cfg of
            f:_ -> f
            _   -> exitWithPanic "Please provide a single verification target."

fixCabalDirs' :: Config -> GHC.DynFlags -> Config
fixCabalDirs' cfg i = cfg { idirs      = nub $ idirs cfg ++ sourceDirs i ++ buildDirs i }
                          { ghcOptions = ghcOptions cfg ++ dbOpts ++ pkOpts
                                      ++ ["-optP-include", "-optP" ++ macroPath i]}
   where
     dbOpts         = ["-package-db " ++ db | db <- packageDbs  i]
     pkOpts         = ["-package "    ++ n  | n  <- packageDeps i] -- SPEED HIT for smaller benchmarks
