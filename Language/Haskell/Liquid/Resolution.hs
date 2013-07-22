module Language.Haskell.Liquid.Resolution where

import Data.Bifunctor
import Control.Applicative
import Data.Maybe
import Text.Printf

import GHC hiding (lookupName)
import CoreMonad
import DynFlags
import DynamicLoading
import FastString
import Finder           ( findImportedModule, cannotFindModule )
import HscMain
import HscTypes         ( HscEnv(..), FindResult(..), ModIface(..), lookupTypeHscEnv )
import Name
import RdrName
import TcRnDriver
import ErrUtils
import Exception
import Panic            ( GhcException(..), throwGhcException )
import RnNames          ( gresFromAvails )
import Outputable
import OccName

import Language.Haskell.Liquid.Measure
import Language.Haskell.Liquid.Parse
import Language.Haskell.Liquid.Types
import qualified Language.Haskell.Liquid.Measure as Ms

import Language.Fixpoint.Types

data ModLoc = Lcl | Pkg deriving Eq

canonicalizeSpec :: ModLoc -> HscEnv -> ModuleName -> BareSpec -> IO BareSpec
canonicalizeSpec ml env mn spec
  = do measures <- mapM (canonicalizeMeas ml env mn) (Ms.measures spec)
       putStrLn $ showpp measures
       return $ spec { measures = measures }

canonicalizeMeas :: ModLoc -> HscEnv -> ModuleName -> Ms.Measure BareType Symbol -> IO (Ms.Measure BareType Symbol)
canonicalizeMeas ml env mn meas
  = do -- mkM (name meas) <$> (canonicalizeType ml env mn $ sort meas) <*> return (eqns meas)
       sort' <- canonicalizeType ml env mn (sort meas)
       eqns' <- mapM resolveCTor $ eqns meas
       putStrLn $ showpp sort'
       return $ mkM (name meas) sort' eqns'
  where resolveCTor def = do ctor <- lookupName ml env mn (symbolString $ Ms.ctor def)
                             return $ def { Ms.ctor = symbol ctor }

canonicalizeType :: ModLoc -> HscEnv -> ModuleName -> BRType a -> IO (BRType a)
canonicalizeType _ e m t@(RVar _ _)   = return t
canonicalizeType l e m (RFun s i o r) = RFun <$> return s
                                             <*> canonicalizeType l e m i
                                             <*> canonicalizeType l e m o
                                             <*> return r
canonicalizeType l e m (RAllT tv t)   = RAllT tv <$> canonicalizeType l e m t
canonicalizeType l e m t@(RAllP _ _)  = return t
canonicalizeType l e m t@(RApp tc as ps r) = RApp <$> lookupName l e m tc
                                                  <*> mapM (canonicalizeType l e m) as
                                                  <*> return ps
                                                  <*> return r
canonicalizeType l e m t@(RCls c as)   = return t
canonicalizeType l e m t@(REx   _ _ _)   = return t
canonicalizeType l e m t@(RExprArg _)   = return t
canonicalizeType l e m t@(RAppTy _ _ _)   = return t
canonicalizeType l e m t@(ROth _)   = return t

lookupName :: ModLoc -> HscEnv -> ModuleName -> String -> IO String
lookupName ml env mod name = do
    rdr <- unLoc <$> hscParseIdentifier env name
    mbName <- lookupRdrName ml env mod rdr
    case mbName of
      Nothing -> tryAlt rdr
      Just n  -> return $ showpp n
  where tryAlt rdr | rdrNameSpace rdr == dataName =
                       let rdr' = setRdrNameSpace rdr tcName
                       in maybe (propOrErr rdr') showpp <$> (lookupRdrName ml env mod rdr')
                   | otherwise = return $ propOrErr rdr
        propOrErr rdr | rdrNameString rdr `elem` ["Prop","()","(,)","[]",":"] = rdrNameString rdr
--                      | isExact rdr = rdrNameString rdr
                      | otherwise = err rdr
        err rdr = error $ moduleNameString mod
                       ++ ":" ++ name
                       ++ ":" ++ showNS (rdrNameSpace rdr)
                       ++ ":" ++ show (isQual rdr)
        rdrNameString = occNameString . rdrNameOcc


addContext m = getContext >>= setContext . (m:)

qualImportDecl mn = (simpleImportDecl mn) { ideclQualified = True }

showNS ns | ns == tcName = "TcClsName"
          | ns == dataName = "DataName"
          | ns == tvName = "TvName"
          | otherwise = "VarName"

mtrace :: Outputable a => a -> IO ()
mtrace = putStrLn . showPpr tracingDynFlags

lookupRdrName :: ModLoc -> HscEnv -> ModuleName -> RdrName -> IO (Maybe Name)
lookupRdrName ml hsc_env mod_name rdr_name = do
    -- First find the package the module resides in by searching exposed packages and home modules
    found_module <- findImportedModule hsc_env mod_name Nothing
    case found_module of
        Found _ mod -> do
            -- Find the exports of the module
            (_, mb_iface) <- getModuleInterface hsc_env mod
            case mb_iface of
                Just iface -> do
                    -- mtrace $ mi_module iface
                    -- mtrace $ mi_decls iface
                    -- mtrace $ mi_exports iface
                    -- Try and find the required name in the exports
                    let decl_spec = ImpDeclSpec { is_mod = mod_name, is_as = mod_name
                                                , is_qual = False, is_dloc = noSrcSpan }
                        provenance = Imported [ImpSpec decl_spec ImpAll]
                        env = case mi_globals iface of
                                Nothing -> mkGlobalRdrEnv (gresFromAvails provenance (mi_exports iface))
                                Just e -> e
--                        Just env' = mi_globals iface
                    case lookupGRE_RdrName rdr_name env of
                        [gre] -> return (Just (gre_name gre))
                        []    -> return Nothing
                        _     -> panic "lookupRdrNameInModule"
                Nothing -> throwCmdLineErrorS dflags $ hsep [ptext (sLit "Could not determine the exports of the module"), ppr mod_name]
        err -> throwCmdLineErrorS dflags $ cannotFindModule dflags mod_name err
  where dflags = hsc_dflags hsc_env
        throwCmdLineErrorS dflags = throwCmdLineError . showSDoc dflags
        throwCmdLineError = throwGhcException . CmdLineError
