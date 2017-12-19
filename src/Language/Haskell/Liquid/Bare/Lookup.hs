{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE OverloadedStrings          #-}

module Language.Haskell.Liquid.Bare.Lookup (
    GhcLookup(..)
  , lookupGhcVar
  , lookupGhcTyCon
  , lookupGhcDnTyCon
  , lookupGhcDataCon
  ) where

import           BasicTypes
import           ConLike
import           DataCon
import           GHC                              (HscEnv)
import           HscMain
import           Name
import           PrelInfo                         (wiredInIds, ghcPrimIds)
import           PrelNames                        (fromIntegerName, smallIntegerName, integerTyConName, basicKnownKeyNames, genericTyConNames) -- , getUnique)
import           Prelude                          hiding (error)
import           RdrName                          (mkQual, rdrNameOcc)
import           SrcLoc                           (SrcSpan, GenLocated(L))
import qualified SrcLoc
import           TcEnv
import           TyCon
import           TysWiredIn
import           Module
import           Finder
import           TcRnMonad
import           IfaceEnv
import           Var hiding (varName)
import           TysPrim
import           RdrName
-- import PrelNames (ioTyConKey)
import           Control.Monad.Except             (catchError, throwError)
import           Control.Monad.State
import qualified Control.Exception as Ex

import           Data.Maybe
import           Text.PrettyPrint.HughesPJ        (text)
import qualified Data.HashMap.Strict              as M
import qualified Data.Text                        as T
import qualified Data.List                        as L
import           Data.Function                    (on)
import           Language.Fixpoint.Types.Names    (symbolText, isPrefixOfSym, lengthSym, symbolString)
import qualified Language.Fixpoint.Types          as F
import           Language.Fixpoint.Misc           as F
import qualified Language.Haskell.Liquid.GHC.Misc as GM
import qualified Language.Haskell.Liquid.Misc     as Misc
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Bare.Env

-- import Debug.Trace (trace)

--------------------------------------------------------------------------------
-- | Querying GHC for Id, Type, Class, Con etc. --------------------------------
--------------------------------------------------------------------------------

class F.Symbolic a => GhcLookup a where
  lookupName :: HscEnv -> ModName -> Maybe NameSpace -> a -> IO [Name]
  srcSpan    :: a -> SrcSpan

instance GhcLookup (Located F.Symbol) where
  lookupName e m ns = symbolLookup e m ns . val
  srcSpan           = GM.sourcePosSrcSpan . loc

instance GhcLookup Name where
  lookupName _ _ _ = return . (:[])
  srcSpan          = nameSrcSpan

instance GhcLookup FieldLabel where
  lookupName e m ns = lookupName e m ns . flSelector
  srcSpan           = srcSpan . flSelector

instance F.Symbolic FieldLabel where
  symbol = F.symbol . flSelector

instance GhcLookup DataName where
  lookupName e m ns = lookupName e m ns . dataNameSymbol
  srcSpan           = GM.fSrcSpanSrcSpan . F.srcSpan

lookupGhcThing :: (GhcLookup a, PPrint b) => String -> (TyThing -> Maybe (Int, b)) -> Maybe NameSpace -> a -> BareM b
lookupGhcThing name f ns x = lookupGhcThing' err f ns x >>= maybe (throwError err) return
  where
    err                 = ErrGhc (srcSpan x) (text msg)
    msg                 = unwords [ "Not in scope:", name, symbolicIdent x]

symbolicIdent :: (F.Symbolic a) => a -> String
symbolicIdent x = "'" ++ symbolicString x ++ "'"


lookupGhcThing' :: (GhcLookup a, PPrint b) => TError e -> (TyThing -> Maybe (Int, b)) -> Maybe NameSpace -> a -> BareM (Maybe b)
lookupGhcThing' _err f ns x = do
  be     <- get
  let env = hscEnv be
--   _      <- liftIO $ putStrLn ("lookupGhcThing: PRE " ++ symbolicString x)
  ns     <- liftIO $ lookupName env (modName be) ns x
--   _      <- liftIO $ putStrLn ("lookupGhcThing: POST " ++ symbolicString x ++ show ns)
  -- mts    <- liftIO $ mapM (fmap (join . fmap f) . hscTcRcLookupName env) ns
  ts     <- liftIO $ catMaybes <$> mapM (hscTcRcLookupName env) ns
  let kts = catMaybes (f <$> ts)
  -- hscTcRcLookupName :: HscEnv -> Name -> IO (Maybe TyThing)
  case Misc.nubHashOn showpp (minBy kts) of
    []  -> return Nothing
    [z] -> return (Just z)
    zs  -> uError $ ErrDupNames (srcSpan x) (pprint (F.symbol x)) (pprint <$> zs)

  -- case filterByName x $ nubHashOn showpp $ catMaybes mts of
    -- []  -> return Nothing
    -- [z] -> return (Just z)
    -- zs  -> case filterByName x zs of
             -- [] -> uError $ ErrDupNames (srcSpan x) (pprint (F.symbol x)) (pprint <$> zs)


minBy :: [(Int, a)] -> [a]
minBy kvs = case kvs' of
              (_, vs):_ -> vs
              []        -> []
  where
    kvs'  = L.sortBy (compare `on` fst) (F.groupList kvs)


_filterByName :: (F.Symbolic a, PPrint b) => a -> [b] -> [b]
_filterByName x = filter (L.isSuffixOf xKey . showpp)
  where
    xKey       = symbolicName x

symbolicName :: (F.Symbolic a) => a -> String
symbolicName = symbolString . GM.dropModuleNamesAndUnique . F.symbol

 -- ghcSymbolString = symbolString . dropModuleUnique

symbolicString :: F.Symbolic a => a -> String
symbolicString = symbolString . F.symbol

-- liftIOErr :: TError e -> IO a -> BareM a
-- liftIOErr e act = liftIO (act `catchError` \_ -> throwError e)

symbolLookup :: HscEnv -> ModName -> Maybe NameSpace -> F.Symbol -> IO [Name]
symbolLookup env mod ns k
  | k `M.member` wiredIn
  = return $ maybeToList $ M.lookup k wiredIn
  | otherwise
  = symbolLookupEnv env mod ns k

wiredIn      :: M.HashMap F.Symbol Name
wiredIn      = M.fromList $ special ++ wiredIns ++ wiredIns' ++ wiredTyCons ++ wiredDcCons
  where
    wiredIns  = [ (F.symbol n, n) | thing <- (wiredInIds ++ ghcPrimIds) {- NV CHECK -}, let n = getName thing ]
    wiredIns' = [ (F.symbol n, n) | n <- (genericTyConNames ++ basicKnownKeyNames)]
    wiredTyCons = [(F.symbol n, n) | n <- getName <$> (primTyCons ++ wiredInTyCons) ]
    wiredDcCons = [(F.symbol n, n) | n <- getName <$>
                      [ falseDataCon, trueDataCon
                      , ltDataCon, eqDataCon, gtDataCon
                      , nilDataCon, consDataCon
                      , charDataCon, intDataCon, wordDataCon, floatDataCon, doubleDataCon]]
    special   = [ ("GHC.Integer.smallInteger", smallIntegerName)
                , ("GHC.Integer.Type.Integer", integerTyConName)
                , ("GHC.Num.fromInteger"     , fromIntegerName ) ]

symbolLookupEnv :: HscEnv -> ModName -> Maybe NameSpace -> F.Symbol -> IO [Name]
symbolLookupEnv env mod ns k = do
  ns <- symbolLookupEnvOrig env mod ns k
  case ns of
    [] -> symbolLookupEnvFull env mod k
    _  -> return ns

safeParseIdentifier :: HscEnv -> String -> IO (SrcLoc.Located RdrName)
safeParseIdentifier env s = hscParseIdentifier env s `Ex.catch` handle
  where
    handle = uError . head . sourceErrors ("GHC error in safeParseIdentifier: " ++ s)

symbolLookupEnvOrig :: HscEnv -> ModName -> Maybe NameSpace -> F.Symbol -> IO [Name]
symbolLookupEnvOrig env mod namespace s
  | isSrcImport mod
  = do let modName = getModName mod
       L _ rn <- safeParseIdentifier env (ghcSymbolString s)
       let rn' = mkQual tcName (moduleNameFS modName,occNameFS $ rdrNameOcc rn)
       res    <- GM.lookupRdrName env modName (makeRdrName rn namespace)
       -- 'safeParseIdentifier' defaults constructors to 'DataCon's, but we also
       -- need to get the 'TyCon's for declarations like @data Foo = Foo Int@.
       res'   <- GM.lookupRdrName env modName rn'
       return $ catMaybes [res, res']
  | otherwise
  = do rn             <- safeParseIdentifier env (ghcSymbolString s)
       (_, lookupres) <- GM.tcRnLookupRdrName env rn
       case lookupres of
         Just ns -> return ns
         _       -> return []



-- TODO: move to misc
makeRdrName :: RdrName -> Maybe NameSpace -> RdrName
makeRdrName (Unqual n) ns = Unqual $ makeOcc n ns
makeRdrName (Qual m n) ns = Qual m $ makeOcc n ns
makeRdrName (Orig m n) ns = Orig m $ makeOcc n ns
makeRdrName (Exact n)  _  = Exact n

makeOcc :: OccName -> Maybe NameSpace -> OccName
makeOcc n Nothing   = n
makeOcc n (Just ns) = mkOccNameFS ns (occNameFS n)

symbolLookupEnvFull :: HscEnv -> ModName -> F.Symbol -> IO [Name]
symbolLookupEnvFull hsc _m s = do
  let (modName, occName) =  ghcSplitModuleName s
  mbMod  <- lookupTheModule hsc modName
  case mbMod of
    Just mod -> liftIO $ F.singleton <$> lookupTheName hsc mod occName
    Nothing  -> return []

lookupTheModule :: HscEnv -> ModuleName -> IO (Maybe Module)
lookupTheModule hsc modName = do
  r <- findImportedModule hsc modName Nothing
  return $ case r of
    Found _ mod -> Just mod
    NotFound {fr_mods_hidden=(unitId:_)} -> Just (mkModule unitId modName)
    _ -> Nothing -- error "i don't know what to do here"

lookupTheName :: HscEnv -> Module -> OccName -> IO Name
lookupTheName hsc mod name = initTcForLookup hsc (lookupOrig mod name)


ghcSplitModuleName :: F.Symbol -> (ModuleName, OccName)
ghcSplitModuleName x = (mkModuleName $ ghcSymbolString m, mkTcOcc $ ghcSymbolString s)
  where
    (m, s)           = GM.splitModuleName x

ghcSymbolString :: F.Symbol -> String
ghcSymbolString = T.unpack . fst . T.breakOn "##" . symbolText
-- ghcSymbolString = symbolString . dropModuleUnique

--------------------------------------------------------------------------------
-- | It's possible that we have already resolved the 'Name' we are looking for,
-- but have had to turn it back into a 'String', e.g. to be used in an 'Expr',
-- as in @{v:Ordering | v = EQ}@. In this case, the fully-qualified 'Name'
-- (@GHC.Types.EQ@) will likely not be in scope, so we store our own mapping of
-- fully-qualified 'Name's to 'Var's and prefer pulling 'Var's from it.
--------------------------------------------------------------------------------
lookupGhcVar :: GhcLookup a => a -> BareM Var
lookupGhcVar x = do
  env <- gets varEnv
  case M.lookup (F.symbol x) env of
    Nothing -> lookupGhcThing "variable" fv (Just varName) x `catchError` \_ ->
               lookupGhcThing "variable or data constructor" fv (Just dataName) x
    Just v  -> return v
  where
    fv (AnId x)                   = Just (0, x)
    fv (AConLike (RealDataCon x)) = Just (1, dataConWorkId x)
    fv _                          = Nothing


lookupGhcDnTyCon :: String -> DataName -> BareM TyCon
lookupGhcDnTyCon src (DnName s)
                   = lookupGhcThing err ftc (Just tcName) s
  where
    err            = "type constructor " ++ src
    ftc (ATyCon x) = Just (0, x)
    ftc (AConLike (RealDataCon x))
              --      | GM.showPpr x == "GHC.Types.[]"
                   = Just (1, {- GM.tracePpr ("lookupGHCTC1 s =" ++ symbolicIdent s ++ " " ++ show ok) $ -}
                              dataConTyCon x)
      where
        res        = dataConTyCon x
        _ok        = res == listTyCon
    ftc _z         = {- GM.tracePpr ("lookupGhcDnTyCon s = " ++ show s ++ "result = " ++ GM.showPpr z) -}
                     Nothing

lookupGhcDnTyCon src (DnCon  s)
                   = lookupGhcThing err ftc (Just tcName) s
  where
    err            = "type constructor " ++ src
    ftc (AConLike (RealDataCon x))
                   = Just (1, dataConTyCon x)
    ftc _          = Nothing

lookupGhcTyCon   ::  GhcLookup a => String -> a -> BareM TyCon
lookupGhcTyCon src s = do
  lookupGhcThing err ftc (Just tcName) s
    -- `catchError` \_ ->
    --  lookupGhcThing err fdc (Just tcName) s
  where
    -- s = trace ("lookupGhcTyCon: " ++ symbolicString _s) _s
    ftc (ATyCon x)
      = Just (0, {- GM.tracePpr ("lookupGHCTC2 s =" ++ symbolicIdent s) -} x)
    -- ftc (AConLike (RealDataCon x))
    --   = Just (1, dataConTyCon x)
    ftc (AConLike (RealDataCon x)) | GM.showPpr x == "GHC.Types.IO"
      = Just (0, dataConTyCon x)
    ftc (AConLike (RealDataCon x))
      = Just (1, promoteDataCon x)
    ftc _
      = Nothing

    err = "type constructor or class\n " ++ src

lookupGhcDataCon :: Located F.Symbol -> BareM DataCon
lookupGhcDataCon dc
  | Just n <- isTupleDC (val dc)
  = return $ tupleDataCon Boxed n
  | val dc == "[]"
  = return nilDataCon
  | val dc == ":"
  = return consDataCon
  | otherwise
  = lookupGhcDataCon' dc

isTupleDC :: F.Symbol -> Maybe Int
isTupleDC zs
  | "(," `isPrefixOfSym` zs
  = Just $ lengthSym zs - 1
  | otherwise
  = Nothing

lookupGhcDataCon' :: (GhcLookup a) => a -> BareM DataCon
lookupGhcDataCon' = lookupGhcThing "data constructor" fdc (Just dataName)
  where
    fdc (AConLike (RealDataCon x)) = Just (0, x)
    fdc _                          = Nothing
