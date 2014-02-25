{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
#!/usr/bin/env runhaskell
module Main where

import           Control.Applicative
import           Data.Generics
import           Data.List
import           System.Environment
import           Text.Printf

import           CoreMonad
import           CoreSyn
import           DynFlags
import           GHC
import           GHC.Paths
import           HscTypes
import qualified Outputable as Out
import           Var

import           Language.Haskell.Liquid.GhcMisc
import           Language.Haskell.Liquid.Misc

getCoreBinds :: FilePath -> IO [CoreBind]
getCoreBinds target = runGhc (Just libdir) $ do
  addTarget =<< guessTarget target Nothing
  flags <- getSessionDynFlags
  inc <- liftIO getIncludeDir
  setSessionDynFlags $ updateDynFlags flags [inc]
  load LoadAllTargets
  modGraph <- getModuleGraph
  case find ((== target) . msHsFilePath) modGraph of
    Just modSummary -> do
      mod_guts <- coreModule <$> (desugarModule =<< typecheckModule =<< parseModule modSummary)
      return   $! mg_binds mod_guts
    Nothing     -> error "Ghc Interface: Unable to get GhcModGuts"


updateDynFlags :: DynFlags -> [FilePath] -> DynFlags
updateDynFlags df ps
  = df { importPaths  = ps ++ importPaths df
       , libraryPaths = ps ++ libraryPaths df
       , profAuto     = ProfAutoCalls
       , ghcLink      = NoLink
       , hscTarget    = HscInterpreted
       , ghcMode      = CompManager
       } `xopt_set` Opt_MagicHash
         `dopt_set` Opt_ImplicitImportQualified


allBinders :: [CoreBind] -> [CoreBind]
allBinders cbs = cbs ++ map bind (concatMap (listify isBinder) cbs)
  where
    bind (Let x _)     = x
    isBinder (Let _ _) = True
    isBinder _         = False


main :: IO ()
main = do
  target <- head <$> getArgs
  binds  <- allBinders <$> getCoreBinds target

  let recs    = concat [bs | Rec bs <- binds]
      recfuns = [v | (v,Lam _ _) <- recs]
      funs    = [v | NonRec v (Lam _ _) <- binds] ++ recfuns

  printf "funs:     %d\n" (length funs)
  printf "recs:     %d\n" (length recs)
  printf "recsFuns: %d\n" (length recfuns)


instance Show Var where
  show = showPpr

instance Show CoreBind where
  show = showPpr

instance Show (Expr CoreBndr) where
  show = showPpr
