{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE OverloadedStrings          #-}

module Language.Haskell.Liquid.Bare.Lookup (
    GhcLookup(..)
  , lookupGhcThing
  , lookupGhcVar
  , lookupGhcTyCon
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
import           TcEnv
import           TyCon
import           TysWiredIn
import           Module
import           Finder
import           TcRnMonad
import           IfaceEnv
import           Var hiding (varName)
import           TysPrim
import RdrName

-- import PrelNames (ioTyConKey)
import           Control.Monad.Except             (catchError, throwError)
import           Control.Monad.State
import           Data.Maybe
import           Text.PrettyPrint.HughesPJ        (text)
import qualified Data.HashMap.Strict              as M
import qualified Data.Text                        as T
import           Language.Fixpoint.Types.Names    (symbolText, isPrefixOfSym, lengthSym, symbolString)
import           Language.Fixpoint.Types          (Symbol, Symbolic(..))
import           Language.Fixpoint.Misc           as F
import           Language.Haskell.Liquid.GHC.Misc (showPpr, splitModuleName, lookupRdrName, sourcePosSrcSpan, tcRnLookupRdrName)
import           Language.Haskell.Liquid.Misc     (firstMaybes)
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Bare.Env

-- import Debug.Trace (trace)

--------------------------------------------------------------------------------
-- | Querying GHC for Id, Type, Class, Con etc. --------------------------------
--------------------------------------------------------------------------------

class Symbolic a => GhcLookup a where
  lookupName :: HscEnv -> ModName -> Maybe NameSpace -> a -> IO [Name]
  srcSpan    :: a -> SrcSpan

instance GhcLookup (Located Symbol) where
  lookupName e m ns = symbolLookup e m ns . val
  srcSpan           = sourcePosSrcSpan . loc

instance GhcLookup Name where
  lookupName _ _ _ = return . (:[])
  srcSpan          = nameSrcSpan

instance GhcLookup FieldLabel where
  lookupName e m ns = lookupName e m ns . flSelector
  srcSpan           = srcSpan . flSelector

instance Symbolic FieldLabel where
  symbol = symbol . flSelector

lookupGhcThing :: (GhcLookup a) => String -> (TyThing -> Maybe b) -> Maybe NameSpace -> a -> BareM b
lookupGhcThing name f ns x = lookupGhcThing' err f ns x >>= maybe (throwError err) return
  where
    err                 = ErrGhc (srcSpan x) (text msg)
    msg                 = unwords [ "Not in scope:", name, "`", symbolicString x, "'"]

lookupGhcThing' :: (GhcLookup a) => TError e -> (TyThing -> Maybe b) -> Maybe NameSpace -> a -> BareM (Maybe b)
lookupGhcThing' _err f ns x = do
  be     <- get
  let env = hscEnv be
--   _      <- liftIO $ putStrLn ("lookupGhcThing: PRE " ++ symbolicString x)
  ns     <- liftIO $ lookupName env (modName be) ns x
--   _      <- liftIO $ putStrLn ("lookupGhcThing: POST " ++ symbolicString x ++ show ns)
  mts    <- liftIO $ mapM (fmap (join . fmap f) . hscTcRcLookupName env) ns
  return  $ firstMaybes mts

symbolicString :: Symbolic a => a -> String
symbolicString = symbolString . symbol

-- liftIOErr :: TError e -> IO a -> BareM a
-- liftIOErr e act = liftIO (act `catchError` \_ -> throwError e)

symbolLookup :: HscEnv -> ModName -> Maybe NameSpace -> Symbol -> IO [Name]
symbolLookup env mod ns k
  | k `M.member` wiredIn
  = return $ maybeToList $ M.lookup k wiredIn
  | otherwise
  = symbolLookupEnv env mod ns k

wiredIn      :: M.HashMap Symbol Name
wiredIn      = M.fromList $ special ++ wiredIns ++ wiredIns' ++ wiredTyCons ++ wiredDcCons
  where
    wiredIns  = [ (symbol n, n) | thing <- (wiredInIds ++ ghcPrimIds) {- NV CHECK -}, let n = getName thing ]
    wiredIns' = [ (symbol n, n) | n <- (genericTyConNames ++ basicKnownKeyNames)]
    wiredTyCons = [(symbol n, n) | n <- getName <$> (primTyCons ++ wiredInTyCons) ]
    wiredDcCons = [(symbol n, n) | n <- getName <$>
                      [ falseDataCon, trueDataCon
                      , ltDataCon, eqDataCon, gtDataCon
                      , nilDataCon, consDataCon
                      , charDataCon, intDataCon, wordDataCon, floatDataCon, doubleDataCon]]
    special   = [ ("GHC.Integer.smallInteger", smallIntegerName)
                , ("GHC.Integer.Type.Integer", integerTyConName)
                , ("GHC.Num.fromInteger"     , fromIntegerName ) ]

symbolLookupEnv :: HscEnv -> ModName -> Maybe NameSpace -> Symbol -> IO [Name]
symbolLookupEnv env mod ns k = do
  ns <- symbolLookupEnvOrig env mod ns k
  case ns of
    [] -> symbolLookupEnvFull env mod k
    _  -> return ns

symbolLookupEnvOrig :: HscEnv -> ModName -> Maybe NameSpace -> Symbol -> IO [Name]
symbolLookupEnvOrig env mod namespace s
  | isSrcImport mod
  = do let modName = getModName mod
       L _ rn <- hscParseIdentifier env $ ghcSymbolString s
       let rn' = mkQual tcName (moduleNameFS modName,occNameFS $ rdrNameOcc rn)
       res    <- lookupRdrName env modName (makeRdrName rn namespace)
       -- 'hscParseIdentifier' defaults constructors to 'DataCon's, but we also
       -- need to get the 'TyCon's for declarations like @data Foo = Foo Int@.
       res'   <- lookupRdrName env modName rn'
       return $ catMaybes [res, res']
  | otherwise
  = do rn             <- hscParseIdentifier env $ ghcSymbolString s
       (_, lookupres) <- tcRnLookupRdrName env rn
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

symbolLookupEnvFull :: HscEnv -> ModName -> Symbol -> IO [Name]
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


ghcSplitModuleName :: Symbol -> (ModuleName, OccName)
ghcSplitModuleName x = (mkModuleName $ ghcSymbolString m, mkTcOcc $ ghcSymbolString s)
  where
    (m, s)           = splitModuleName x

ghcSymbolString :: Symbol -> String
ghcSymbolString = T.unpack . fst . T.breakOn "##" . symbolText
-- ghcSymbolString = symbolString . dropModuleUnique

-- | It's possible that we have already resolved the 'Name' we are looking for,
-- but have had to turn it back into a 'String', e.g. to be used in an 'Expr',
-- as in @{v:Ordering | v = EQ}@. In this case, the fully-qualified 'Name'
-- (@GHC.Types.EQ@) will likely not be in scope, so we store our own mapping of
-- fully-qualified 'Name's to 'Var's and prefer pulling 'Var's from it.
lookupGhcVar :: GhcLookup a => a -> BareM Var
lookupGhcVar x
  = do env <- gets varEnv
       case M.lookup (symbol x) env of
         Nothing -> lookupGhcThing "variable" fv (Just varName) x `catchError` \_ ->
                    lookupGhcThing "variable or data constructor" fv (Just dataName) x
         Just v  -> return v
  where
    fv (AnId x)                   = Just x
    fv (AConLike (RealDataCon x)) = Just $ dataConWorkId x
    fv _                          = Nothing


lookupGhcTyCon   ::  GhcLookup a => String -> a -> BareM TyCon
lookupGhcTyCon src s = do
  lookupGhcThing err ftc (Just tcName) s  `catchError` \_ ->
   lookupGhcThing err fdc (Just tcName) s
  where
    -- s = trace ("lookupGhcTyCon: " ++ symbolicString _s) _s
    ftc (ATyCon x)
      = Just x
    ftc _
      = Nothing

    fdc (AConLike (RealDataCon x)) | showPpr x == "GHC.Types.IO"  -- getUnique x `hasKey` ioTyConKey
      = Just $ dataConTyCon x
    fdc (AConLike (RealDataCon x)) --  isJust $ promoteDataCon_maybe x
      = Just $ promoteDataCon x
    fdc _
      = Nothing

    err = "type constructor or class\n " ++ src

lookupGhcDataCon :: Located Symbol -> BareM DataCon
lookupGhcDataCon dc
  | Just n <- isTupleDC (val dc)
  = return $ tupleDataCon Boxed n
  | val dc == "[]"
  = return nilDataCon
  | val dc == ":"
  = return consDataCon
  | otherwise
  = lookupGhcDataCon' dc

isTupleDC :: Symbol -> Maybe Int
isTupleDC zs
  | "(," `isPrefixOfSym` zs
  = Just $ lengthSym zs - 1
  | otherwise
  = Nothing

lookupGhcDataCon' :: (GhcLookup a) => a -> BareM DataCon
lookupGhcDataCon' = lookupGhcThing "data constructor" fdc (Just dataName)
  where
    fdc (AConLike (RealDataCon x)) = Just x
    fdc _                          = Nothing
