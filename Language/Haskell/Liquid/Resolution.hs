{-# LANGUAGE TupleSections, TypeSynonymInstances, FlexibleInstances #-}
module Language.Haskell.Liquid.Resolution
  (lookupRdrName, qualImportDecl, resolveSpec, addContext, runResolveM)
  where

import Control.Applicative
import Control.Arrow
import Control.Monad.Reader
import Data.Char
import Data.Maybe
import qualified Data.HashMap.Strict as M
import Text.Printf

import GHC hiding (lookupName, Located)
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
import Outputable hiding (showPpr)
import OccName

--import Language.Haskell.Liquid.Bare
import Language.Haskell.Liquid.GhcMisc (showPpr)
import qualified Language.Haskell.Liquid.Measure as Ms
import Language.Haskell.Liquid.Parse
import Language.Haskell.Liquid.Types

import Language.Fixpoint.Types hiding (SESearch(..))


type ResolveM = ReaderT (HscEnv,ModuleName) IO

runResolveM :: HscEnv -> ModuleName -> ResolveM a -> IO a
runResolveM e m x = runReaderT x (e,m)

resolveSpec :: HscEnv -> ModuleName -> BareSpec -> IO BareSpec
resolveSpec e m spec = runResolveM e m $ do
  measures   <- mapM resolveMeas (Ms.measures spec)
  sigs       <- mapM resolveSig  (Ms.sigs spec)
  invariants <- mapM resolveInv  (Ms.invariants spec)
  dataDecls  <- mapM resolveData (Ms.dataDecls spec)
  embeds     <- resolveEmbed     (Ms.embeds spec)
  qualifiers <- mapM resolveQual (Ms.qualifiers spec)
  return $ spec { Ms.measures   = measures
                , Ms.sigs       = sigs
                , Ms.invariants = invariants
                , Ms.dataDecls  = dataDecls
                , Ms.embeds     = embeds
                , Ms.qualifiers = qualifiers
                }

resolveMeas meas
  = Ms.mkM (Ms.name meas) <$> resolve (Ms.sort meas)
                          <*> mapM resolveCTor (Ms.eqns meas)
  where
    resolveCTor def = do ctor <- lookupName (symbolString $ Ms.ctor def)
                         return $ def { Ms.ctor = symbol ctor }

resolveSig (l, ty) = (l,) <$> resolve ty

resolveInv (Loc x ty) = Loc x <$> resolve ty

resolveData (D n tvs pvs dcs sp d)
  = D <$> lookupName n <*> return tvs <*> return pvs <*> mapM resolveDC dcs
      <*> return sp <*> return d
  where
    resolveDC (dc, args) = (,) <$> lookupName dc <*> mapM resolveSig args

resolveEmbed emb = M.fromList <$> mapM resolveKey (M.toList emb)
  where
    resolveKey (Loc x k, v) = (,v) . Loc x <$> lookupName k

resolveQual (Q n ps b) = Q n <$> mapM (secondM resolve) ps <*> resolvePred b

class Resolvable a where
  resolve :: a -> ResolveM a

instance Resolvable Sort where
  resolve FInt         = return FInt
  resolve FNum         = return FNum
  resolve s@(FObj _)   = return s --FObj . S <$> lookupName env m s
  resolve s@(FVar _)   = return s
  resolve (FFunc i ss) = FFunc i <$> mapM resolve ss
  resolve (FApp tc ss) = FApp <$> (stringFTycon <$> lookupName (fTyconString tc))
                              <*> mapM resolve ss

firstM  f (a,b) = (,b) <$> f a
secondM f (a,b) = (a,) <$> f b
thirdM  f (a,b,c) = (a,b,) <$> f c

instance (Resolvable a) => Resolvable (BRType a) where
  resolve (RVar v t)     = RVar v <$> resolve t
  resolve (RFun s i o r) = RFun s <$> resolve i
                                  <*> resolve o
                                  <*> resolve r
  resolve (RAllT tv t) = RAllT tv <$> resolve t
  resolve (RAllP p t)  = RAllP <$> resolve p <*> resolve t
  resolve (RApp tc as ps r) = RApp <$> lookupName tc
                                   <*> mapM resolve as
                                   <*> mapM resolve ps
                                   <*> resolve r
  resolve (RCls c as)     = RCls <$> lookupName c
                                 <*> mapM resolve as
  resolve (RAllE b a ty)  = REx b <$> resolve a
                                  <*> resolve ty
  resolve (REx b a ty)    = REx b <$> resolve a
                                  <*> resolve ty
  resolve (RExprArg e)    = RExprArg <$> resolveExpr e
  resolve (RAppTy a r rt) = RAppTy <$> resolve a
                                   <*> resolve r
                                   <*> resolve rt
  resolve t@(ROth _)      = return t


instance (Resolvable t, Resolvable s, Resolvable m) => Resolvable (Ref t s m) where
  resolve (RMono vs r) = RMono <$> mapM (secondM resolve) vs <*> resolve r
  resolve (RPoly vs t) = RPoly <$> mapM (secondM resolve) vs <*> resolve t


instance Resolvable (UReft Reft) where
  resolve (U r p) = U <$> resolveReft r <*> resolvePredicate p
    where
      resolveReft (Reft (s, ras)) = Reft . (s,) <$> mapM resolveRefa ras

      resolveRefa (RConc p) = RConc <$> resolvePred p
      resolveRefa kv        = return kv

resolvePred (PAnd ps)       = PAnd <$> mapM resolvePred ps
resolvePred (POr  ps)       = POr  <$> mapM resolvePred ps
resolvePred (PNot p)        = PNot <$> resolvePred p
resolvePred (PImp p q)      = PImp <$> resolvePred p <*> resolvePred q
resolvePred (PIff p q)      = PIff <$> resolvePred p <*> resolvePred q
resolvePred (PBexp b)       = PBexp <$> resolveExpr b
resolvePred (PAtom r e1 e2) = PAtom r <$> resolveExpr e1 <*> resolveExpr e2
resolvePred (PAll vs p)     = PAll <$> mapM (secondM resolve) vs
                                   <*> resolvePred p
resolvePred p               = return p


resolvePredicate (Pr pvs) = Pr <$> mapM resolve pvs
  where

instance (Resolvable t) => Resolvable (PVar t) where
  resolve (PV n t as) = PV n t <$> mapM (thirdM resolveExpr) as


resolveExpr v@(EVar (S s))
    | isCon s   = EVar . S <$> lookupName s
    | otherwise = return v
resolveExpr v@(EApp (S s) es)
    | isCon s   = EApp . S <$> lookupName s <*> es'
    | otherwise = EApp (S s) <$> es'
    where es'   = mapM resolveExpr es
resolveExpr (EBin o e1 e2)
    = EBin o <$> resolveExpr e1 <*> resolveExpr e2
resolveExpr (EIte p e1 e2)
    = EIte <$> resolvePred p <*> resolveExpr e1 <*> resolveExpr e2
resolveExpr (ECst x s) = ECst <$> resolveExpr x <*> resolve s
resolveExpr x          = return x

-- lookupDcId s = ask >>= lookup
--   where
--     lookup (env,mod,Qual) = do
--       rdr      <- unLoc <$> (liftIO $ hscParseIdentifier env s)
--       Just n   <- liftIO $ lookupRdrName env mod rdr
--       Just res <- liftIO $ hscTcRcLookupName env n
--       return $ case res of
--         AnId x -> showpp x
--         ADataCon x -> showpp $ dataConWrapId x
--         x -> error $ "lookupDcId: " ++ s ++ " -> " ++ showPpr x
--     lookup (env,mod,Other) = lookupName s

isCon (c:cs) = isUpper c
isCon []     = False

instance Resolvable () where
  resolve () = return ()

instance Resolvable String where
  resolve = lookupName

lookupName :: String -> ResolveM String
lookupName name = ask >>= liftIO . go
  where
    go (env,mod) = do
      rdr <- unLoc <$> hscParseIdentifier env name
      if isExact rdr
        then return $ rdrNameString rdr
        else maybe (tryAlt rdr) (return.showpp) =<< lookupRdrName env mod rdr
     where
       tryAlt rdr | rdrNameSpace rdr == dataName =
                      let rdr' = setRdrNameSpace rdr tcName
                      in maybe (showPpr rdr') showpp <$> lookupRdrName env mod rdr'
                  | otherwise = return $ propOrErr rdr
       propOrErr rdr | n == "Prop" = "Prop"
                     -- | n `M.member` wiredIn = showpp $ wiredIn M.! n
                     -- | isQual rdr = n
                     | otherwise = err rdr
                     where n = rdrNameString rdr
       err rdr = error $ moduleNameString mod
                      ++ ":" ++ name
                      ++ ":" ++ showNS (rdrNameSpace rdr)
       rdrNameString = occNameString . rdrNameOcc


addContext m = getContext >>= setContext . (m:)

qualImportDecl mn = (simpleImportDecl mn) { ideclQualified = True }

showNS ns | ns == tcName = "TcClsName"
          | ns == dataName = "DataName"
          | ns == tvName = "TvName"
          | otherwise = "VarName"

mtrace :: Outputable a => a -> IO ()
mtrace = putStrLn . showPpr

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
