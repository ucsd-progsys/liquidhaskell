{-# LANGUAGE TupleSections #-}
module Language.Haskell.Liquid.Resolution where

import Control.Applicative
import Control.Arrow
import Data.Maybe
import qualified Data.HashMap.Strict as S
import Text.Printf

import GHC hiding (lookupName, Located)
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

resolveSpec :: HscEnv -> ModuleName -> BareSpec -> IO BareSpec
resolveSpec env mn spec
  = do measures   <- mapM (resolveMeas env mn) (Ms.measures spec)
       sigs       <- mapM (resolveSig env mn)  (Ms.sigs spec)
       invariants <- mapM (resolveInv env mn)  (Ms.invariants spec)
       dataDecls  <- mapM (resolveData env mn) (Ms.dataDecls spec)
       embeds     <- resolveEmbed env mn       (Ms.embeds spec)
       qualifiers <- mapM (resolveQual env mn) (Ms.qualifiers spec)
       return $ spec { Ms.measures   = measures
                     , Ms.sigs       = sigs
                     , Ms.invariants = invariants
                     , Ms.dataDecls  = dataDecls
                     , Ms.embeds     = embeds
                     , Ms.qualifiers = qualifiers
                     }

resolveMeas :: HscEnv -> ModuleName -> Ms.Measure BareType Symbol -> IO (Ms.Measure BareType Symbol)
resolveMeas env mn meas
  = do -- mkM (name meas) <$> (resolveType ml env mn $ sort meas) <*> return (eqns meas)
       sort' <- resolveType env mn (sort meas)
       eqns' <- mapM resolveCTor $ eqns meas
       return $ mkM (name meas) sort' eqns'
  where resolveCTor def = do ctor <- lookupName env mn (symbolString $ Ms.ctor def)
                             return $ def { Ms.ctor = symbol ctor }

resolveSig env m (l, ty) = (l,) <$> resolveType env m ty

resolveInv env m (Loc x ty) = Loc x <$> resolveType env m ty

resolveData env m (D n tvs pvs dcs sp d)
  = D <$> lookupName env m n <*> return tvs <*> return pvs <*> mapM resolveDC dcs
      <*> return sp <*> return d
  where
    resolveDC (dc, args) = (,) <$> lookupName env m dc <*> mapM (resolveSig env m) args

resolveEmbed env m emb = S.fromList <$> mapM resolveKey (S.toList emb)
  where
    resolveKey (Loc x k, v) = (,v) . Loc x <$> lookupName env m k

resolveQual env m (Q n ps b) = Q n <$> mapM (secondM (resolveSort env m)) ps <*> return b

resolveSort env m FInt         = return FInt
resolveSort env m FNum         = return FNum
resolveSort env m (FObj (S s)) = FObj . S <$> lookupName env m s
resolveSort env m (FVar i)     = return $ FVar i
resolveSort env m (FFunc i ss) = FFunc i <$> mapM (resolveSort env m) ss
resolveSort env m (FApp tc ss) = FApp <$> (stringFTycon <$> lookupName env m (fTyconString tc))
                                      <*> mapM (resolveSort env m) ss

firstM  f (a,b) = (,b) <$> f a
secondM f (a,b) = (a,) <$> f b

resolveType :: HscEnv -> ModuleName -> BRType a -> IO (BRType a)
resolveType e m t@(RVar _ _)   = return t
resolveType e m (RFun s i o r) = RFun <$> return s
                                      <*> resolveType e m i
                                      <*> resolveType e m o
                                      <*> return r
resolveType e m (RAllT tv t)   = RAllT tv <$> resolveType e m t
resolveType e m t@(RAllP _ _)  = return t
resolveType e m t@(RApp tc as ps r) = RApp <$> lookupName e m tc
                                           <*> mapM (resolveType e m) as
                                           <*> return ps
                                           <*> return r
resolveType e m t@(RCls c as)  = RCls <$> lookupName e m c
                                      <*> mapM (resolveType e m) as
resolveType e m t@(REx b a ty)  = REx b <$> resolveType e m a
                                        <*> resolveType e m ty
resolveType e m t@(RExprArg _) = return t
resolveType e m t@(RAppTy a r rt) = RAppTy <$> resolveType e m a
                                           <*> resolveType e m r
                                           <*> return rt
resolveType e m t@(ROth _)   = return t

lookupName :: HscEnv -> ModuleName -> String -> IO String
lookupName env mod name = do
    rdr <- unLoc <$> hscParseIdentifier env name
    mbName <- lookupRdrName env mod rdr
    case mbName of
      Nothing -> tryAlt rdr
      Just n  -> return $ showpp n
  where tryAlt rdr | rdrNameSpace rdr == dataName =
                       let rdr' = setRdrNameSpace rdr tcName
                       in maybe (propOrErr rdr') showpp <$> (lookupRdrName env mod rdr')
                   | otherwise = return $ propOrErr rdr
        propOrErr rdr | rdrNameString rdr `elem` ["Prop","()","(,)","[]",":"] = rdrNameString rdr
--                      | isExact rdr = rdrNameString rdr
                      | otherwise = rdrNameString rdr
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

-- slightly modified version of DynamicLoading.lookupRdrNameInModule
lookupRdrName :: HscEnv -> ModuleName -> RdrName -> IO (Maybe Name)
lookupRdrName hsc_env mod_name rdr_name = do
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
                    case lookupGRE_RdrName rdr_name env of
                        [gre] -> return (Just (gre_name gre))
                        []    -> return Nothing
                        _     -> panic "lookupRdrNameInModule"
                Nothing -> throwCmdLineErrorS dflags $ hsep [ptext (sLit "Could not determine the exports of the module"), ppr mod_name]
        err -> throwCmdLineErrorS dflags $ cannotFindModule dflags mod_name err
  where dflags = hsc_dflags hsc_env
        throwCmdLineErrorS dflags = throwCmdLineError . showSDoc dflags
        throwCmdLineError = throwGhcException . CmdLineError
