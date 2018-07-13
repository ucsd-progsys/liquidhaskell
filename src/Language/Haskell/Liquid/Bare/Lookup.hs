{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE OverloadedStrings          #-}

module Language.Haskell.Liquid.Bare.Lookup (
    GhcLookup(..)
  , lookupGhcVar
  , lookupGhcWrkVar
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
import           PrelNames                        (fromIntegerName, smallIntegerName, integerTyConName, basicKnownKeyNames, genericTyConNames) 
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
import qualified Language.Fixpoint.Types.Names    as Names -- (symbolText, isPrefixOfSym, lengthSym, symbolString)
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
  srcSpan           = srcSpan           . flSelector

instance F.Symbolic FieldLabel where
  symbol = F.symbol . flSelector

instance GhcLookup DataName where
  lookupName e m ns = lookupName e m ns .  dataNameSymbol
  srcSpan           = GM.fSrcSpanSrcSpan . F.srcSpan

lookupGhcThing :: (GhcLookup a, PPrint b) => String -> (TyThing -> Maybe (Int, b)) -> Maybe NameSpace -> a -> BareM b
lookupGhcThing name f ns x = lookupGhcThing' f ns x >>= maybe (throwError err) return
  where
    err                 = ErrGhc (srcSpan x) (text msg)
    msg                 = unwords [ "Not in scope:", name, symbolicIdent x]

symbolicIdent :: (F.Symbolic a) => a -> String
symbolicIdent x = "'" ++ symbolicString x ++ "'"



lookupGhcThing' :: (GhcLookup a, PPrint b) => (TyThing -> Maybe (Int, b)) -> Maybe NameSpace -> a -> BareM (Maybe b)
lookupGhcThing' f ns x = do
  be     <- get
  let env = hscEnv be
  ns     <- liftIO $ lookupName env (modName be) ns x
  ts     <- liftIO $ catMaybes <$> mapM (hscTcRcLookupName env) (GM.tracePpr ("OHO FOUND STUFF 1" ++ show (F.symbol x)) ns)
  ts'    <- map (AConLike . RealDataCon)  . lookupEnv x <$> gets famEnv
  let kts = catMaybes (f <$> GM.tracePpr ("OHO FOUND STUFF 2" ++ show (F.symbol x)) (ts ++ ts'))
  case Misc.nubHashOn showpp (minBy kts) of
    []   -> return Nothing
    [z]  -> return (Just z)
    zs   -> uError $ ErrDupNames (srcSpan x) (pprint (F.symbol x)) (pprint <$> zs)

lookupEnv :: (GhcLookup a) => a -> M.HashMap F.Symbol b -> [b]
lookupEnv x env = maybeToList (M.lookup (F.symbol x) env)

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
symbolicName = F.symbolString . GM.dropModuleNamesAndUnique . F.symbol

 -- ghcSymbolString = symbolString . dropModuleUnique

symbolicString :: F.Symbolic a => a -> String
symbolicString = F.symbolString . F.symbol

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
    wiredIns  = [ (F.symbol n, n) | thing <- wiredInIds ++ ghcPrimIds, let n = getName thing ]
    wiredIns' = [ (F.symbol n, n) | n <- genericTyConNames ++ basicKnownKeyNames ]
    wiredTyCons = F.tracepp "WIRED-TYCONS" [(F.symbol n, n) | n <- getName <$> (primTyCons ++ wiredInTyCons) ]
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
ghcSymbolString = T.unpack . fst . T.breakOn "##" . F.symbolText

--------------------------------------------------------------------------------
-- | It's possible that we have already resolved the 'Name' we are looking for,
-- but have had to turn it back into a 'String', e.g. to be used in an 'Expr',
-- as in @{v:Ordering | v = EQ}@. In this case, the fully-qualified 'Name'
-- (@GHC.Types.EQ@) will likely not be in scope, so we store our own mapping of
-- fully-qualified 'Name's to 'Var's and prefer pulling 'Var's from it.
--------------------------------------------------------------------------------
lookupGhcVar :: (GhcLookup a) => a -> BareM Var
lookupGhcVar x = do
  let xSym = F.symbol x
  case lookupWiredDataCon xSym of 
    Just dc -> return (dataConWorkId dc)
    Nothing -> do
      env <- gets varEnv
      case M.lookup xSym env of
        Nothing -> lookupGhcThing "variable" fv (Just varName) x `catchError` \_ ->
                   lookupGhcThing "variable or data constructor" fv (Just dataName) x
        Just v  -> return v
      where
        fv (AnId x)                   = Just (0, x)
        fv (AConLike (RealDataCon x)) = Just (1, dataConWorkId x)
        fv _                          = Nothing

-- | Specialized version of the above to deal with 'WorkerId' of the form 
--   'Foo.$WCtor' which crash the GHC parser. Sigh.

lookupGhcWrkVar :: F.LocSymbol -> BareM Var
lookupGhcWrkVar wx = 
  lookupGhcThing "variable" fv (Just varName) x `catchError` \_ ->
  lookupGhcThing "variable or data constructor (wrk)" fv (Just dataName) x
  where
    x                             = F.notracepp msg (fixWorkSymbol <$> wx)
    msg                           = "lookupGhcWrkVar wx = " ++ F.showpp wx
    fv (AnId z)                   = Just (0, z)
    fv (AConLike (RealDataCon z)) = Just (1, dataConWorkId z)
    fv _                          = Nothing

fixWorkSymbol :: F.Symbol -> F.Symbol 
fixWorkSymbol s   = maybe s reQual (F.stripPrefix wrkPrefix x) 
  where
    isQual        = F.lengthSym m > 0
    reQual z
      | isQual    = GM.qualifySymbol m z 
      | otherwise = z 
    (m, x)        = GM.splitModuleName s 
    wrkPrefix     = "$W"

lookupGhcDnTyCon :: String -> DataName -> BareM TyCon
lookupGhcDnTyCon src (DnName s)
                   = lookupGhcThing err ftc (Just tcName) s
  where
    err            = "type constructor " ++ src
    ftc (ATyCon x) = Just (0, x)
    ftc (AConLike (RealDataCon x))
                   = Just (1, dataConTyCon x)
      where
        res        = dataConTyCon x
        _ok        = res == listTyCon
    ftc _z         = GM.notracePpr ("lookupGhcDnTyCon 1 s = " ++ show s ++ "result = " ++ GM.showPpr _z)
                     $ Nothing

lookupGhcDnTyCon src (DnCon  s)
                   = lookupGhcThing err ftc (Just tcName) s
  where
    err            = "type konstructor " ++ src
    ftc (AConLike (RealDataCon x))
                   = GM.notracePpr ("lookupGhcDnTyCon 1 s = " ++ show s ++ "result = " ++ GM.showPpr x)
                     $ Just (1, dataConTyCon x)
    ftc (AConLike _z)
                   = GM.notracePpr ("lookupGhcDnTyCon 2 s = " ++ show s ++ "result = " ++ GM.showPpr _z)
                     $ Nothing
    ftc (AnId _z)
                   = GM.notracePpr ("lookupGhcDnTyCon 3 s = " ++ show s ++ "result = " ++ GM.showPpr _z)
                     $ Nothing
    ftc (ATyCon _z) = GM.notracePpr ("lookupGhcDnTyCon 4 s = " ++ show s ++ "result = " ++ GM.showPpr _z)
                     $ Nothing
    ftc _z          = GM.notracePpr ("lookupGhcDnTyCon 5 s = " ++ show s ++ "result = " ++ GM.showPpr _z)
                     $ Nothing

lookupGhcTyCon   ::  GhcLookup a => String -> a -> BareM TyCon
lookupGhcTyCon src s = do
  case lookupWiredTyCon (F.symbol s) of 
    Just tc -> return tc 
    Nothing -> lookupGhcThing err ftc (Just tcName) s
  where
    ftc (ATyCon x)
      = Just (0, x)
    ftc (AConLike (RealDataCon x)) | GM.showPpr x == "GHC.Types.IO"
      = Just (0, dataConTyCon x)
    ftc (AConLike (RealDataCon x))
      = Just (1, promoteDataCon x)
    ftc _
      = Nothing
    err = "type constructor or class\n " ++ src

lookupGhcDataCon :: Located F.Symbol -> BareM DataCon
lookupGhcDataCon dc = 
  case lookupWiredDataCon (F.tracepp "lookupGhcDatacon" $ val dc) of
    Just x  -> return x
    Nothing -> lookupGhcDataCon' dc

lookupWiredDataCon :: F.Symbol -> Maybe DataCon
lookupWiredDataCon x = M.lookup x wiredDataConEnv

{- 
wiredDataCons :: M.HashMap F.Symbol DataCon 
wiredDataCons = M.fromList 
   $ (nTupleDataCon <$> [2..10])
  ++ [ ("[]"              , nilDataCon    )
     , (":"               , consDataCon   )
     , ("GHC.Base.Nothing", nothingDataCon)
     , ("GHC.Base.Just"   , justDataCon   )
     , ("I#"              , intDataCon    )
     , ("C#"              , charDataCon   )
     ]
-} 

wiredDataConEnv :: M.HashMap F.Symbol DataCon 
wiredDataConEnv = M.fromList [ (F.symbol dc, dc) | dc <- wiredInDCs ] 
  where
    wiredInDCs :: [DataCon]
    wiredInDCs =  [ tupleDataCon Boxed n | n <- [2..10] ] 
               ++ [ nilDataCon    
                  , consDataCon   
                  , nothingDataCon
                  , justDataCon   
                  , intDataCon    
                  , charDataCon   
                  ]

lookupWiredTyCon :: F.Symbol -> Maybe TyCon 
lookupWiredTyCon x = M.lookup x wiredTyConEnv

wiredTyConEnv :: M.HashMap F.Symbol TyCon 
wiredTyConEnv = M.fromList [(F.symbol tc, tc) | tc <- primTyCons ++ wiredInTyCons ]
     
_nTupleDataCon :: Int -> (F.Symbol, DataCon) 
_nTupleDataCon n = (x, dc)  
  where 
    x           = F.symbol $ "(" ++ replicate (n - 1) ',' ++  ")"
    dc          = tupleDataCon Boxed n 

lookupGhcDataCon' :: (GhcLookup a) => a -> BareM DataCon
lookupGhcDataCon' = lookupGhcThing "data constructor" fdc (Just dataName)
  where
    fdc (AConLike (RealDataCon x)) = Just (0, x)
    fdc _                          = Nothing
