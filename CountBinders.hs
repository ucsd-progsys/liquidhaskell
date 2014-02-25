{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
#!/usr/bin/env runhaskell
module Main where


import           Control.Applicative
import           Data.Function
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
import           Type
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


recsAndFuns :: [CoreBind] -> ([Var],[Var],[Var])
recsAndFuns binds = (recs,recfuns,funs)
  where
    recs    = [v | Rec bs <- binds, (v,_)  <- bs]
    recfuns = filter isFun recs
    -- GHC does transforms recursive functions (at least with tyvars)
    -- into a let binding that quantifies over the tyvar followed by a
    -- letrec that defines the function, e.g.
    --     let foo = \ @a -> { letrec foo = ... in foo }
    -- but we don't want to count foo as rec and nonrec
    funs    = nubBy ((==) `on` getOccName)
            $ [v | NonRec v _ <- binds, isFun v]
           ++ recfuns
    isFun   = isFunTy . snd . splitForAllTys . varType


main :: IO ()
main = do
  target <- head <$> getArgs
  binds  <- allBinders <$> getCoreBinds target

  let (recs,recfuns,funs) = recsAndFuns binds

  printf "funs:     %d\n" (length funs)
  printf "recs:     %d\n" (length recs)
  printf "recsFuns: %d\n" (length recfuns)


instance Show Var where
  show = showPpr

instance Show CoreBind where
  show = showPpr

instance Show (Expr CoreBndr) where
  show = showPpr
