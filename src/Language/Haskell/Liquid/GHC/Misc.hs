{-# LANGUAGE CPP                       #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE ViewPatterns              #-}

-- | This module contains a wrappers and utility functions for
-- accessing GHC module information. It should NEVER depend on
-- ANY module inside the Language.Haskell.Liquid.* tree.

module Language.Haskell.Liquid.GHC.Misc where

import PrelNames (fractionalClassKeys)
import Class     (classKey)

import           Debug.Trace

import           Avail                        (availsToNameSet)
import           BasicTypes                   (Arity)
import           CoreSyn                      hiding (Expr, sourceName)
import qualified CoreSyn as Core
import           CostCentre
import           GHC                          hiding (L)
import           HscTypes                     (Dependencies, ImportedMods, ModGuts(..), HscEnv(..), FindResult(..))
import           Kind                         (superKind)
import           NameSet                      (NameSet)
import           SrcLoc                       (mkRealSrcLoc, mkRealSrcSpan, srcSpanFileName_maybe)
import           Bag
import           ErrUtils
import           CoreLint
import           CoreMonad

import           Text.Parsec.Pos              (sourceName, sourceLine, sourceColumn, newPos)

import           Name                         (mkInternalName, getSrcSpan, nameModule_maybe)
import           Module                       (moduleNameFS)
import           OccName                      (mkTyVarOcc, mkVarOcc, mkTcOcc, occNameFS)
import           Unique
import           Finder                       (findImportedModule, cannotFindModule)
import           Panic                        (throwGhcException)
import           FastString
import           TcRnDriver
-- import           TcRnTypes


import           RdrName
import           Type                         (liftedTypeKind)
import           TypeRep
import           Var
import           IdInfo
import qualified TyCon                        as TC
import           Data.Char                    (isLower, isSpace)
import           Data.Maybe                   (fromMaybe)
import           Data.Hashable
import qualified Data.HashSet                 as S
import           Data.Aeson
import qualified Data.Text.Encoding           as T
import qualified Data.Text                    as T
import           Control.Arrow                (second)
import           Control.Monad                ((>=>))
import           Outputable                   (Outputable (..), text, ppr)
import qualified Outputable                   as Out
import           DynFlags
import qualified Text.PrettyPrint.HughesPJ    as PJ
import           Language.Fixpoint.Types      hiding (L, Loc (..), SrcSpan, Constant, SESearch (..))
import           Language.Fixpoint.Misc       (safeHead, safeLast, safeInit)
import           Language.Haskell.Liquid.Desugar710.HscMain



-----------------------------------------------------------------------
--------------- Datatype For Holding GHC ModGuts ----------------------
-----------------------------------------------------------------------

data MGIModGuts = MI {
    mgi_binds     :: !CoreProgram
  , mgi_module    :: !Module
  , mgi_deps      :: !Dependencies
  , mgi_dir_imps  :: !ImportedMods
  , mgi_rdr_env   :: !GlobalRdrEnv
  , mgi_tcs       :: ![TyCon]
  , mgi_fam_insts :: ![FamInst]
  , mgi_exports   :: !NameSet
  , mgi_cls_inst  :: !(Maybe [ClsInst])
  }

miModGuts cls mg  = MI {
    mgi_binds     = mg_binds mg
  , mgi_module    = mg_module mg
  , mgi_deps      = mg_deps mg
  , mgi_dir_imps  = mg_dir_imps mg
  , mgi_rdr_env   = mg_rdr_env mg
  , mgi_tcs       = mg_tcs mg
  , mgi_fam_insts = mg_fam_insts mg
  , mgi_exports   = availsToNameSet $ mg_exports mg
  , mgi_cls_inst  = cls
  }

--------------------------------------------------------------------------------
-- | Encoding and Decoding Location --------------------------------------------
--------------------------------------------------------------------------------
srcSpanTick :: Module -> SrcSpan -> Tickish a
srcSpanTick m sp = ProfNote (AllCafsCC m sp) False True

{-
tickSrcSpan ::  Outputable a => Tickish a -> SrcSpan
tickSrcSpan z
  | sp == noSrcSpan = traceShow ("tickSrcSpan:" ++ showPpr z) sp
  | otherwise       = sp
  where
    sp              = tickSrcSpan' z
-}

tickSrcSpan ::  Outputable a => Tickish a -> SrcSpan
tickSrcSpan (ProfNote cc _ _) = cc_loc cc
tickSrcSpan (SourceNote ss _) = RealSrcSpan ss
tickSrcSpan _                 = noSrcSpan

-----------------------------------------------------------------------
--------------- Generic Helpers for Accessing GHC Innards -------------
-----------------------------------------------------------------------

stringTyVar :: String -> TyVar
stringTyVar s = mkTyVar name liftedTypeKind
  where name = mkInternalName (mkUnique 'x' 24)  occ noSrcSpan
        occ  = mkTyVarOcc s

stringVar :: String -> Type -> Var
stringVar s t = mkLocalVar VanillaId name t vanillaIdInfo
   where
      name = mkInternalName (mkUnique 'x' 25) occ noSrcSpan
      occ  = mkVarOcc s

stringTyCon :: Char -> Int -> String -> TyCon
stringTyCon = stringTyConWithKind superKind

stringTyConWithKind :: Kind -> Char -> Int -> String -> TyCon
stringTyConWithKind k c n s = TC.mkKindTyCon name k
  where
    name          = mkInternalName (mkUnique c n) occ noSrcSpan
    occ           = mkTcOcc s

hasBaseTypeVar = isBaseType . varType

-- same as Constraint isBase
isBaseType (ForAllTy _ t)  = isBaseType t
isBaseType (TyVarTy _)     = True
isBaseType (TyConApp _ ts) = all isBaseType ts
isBaseType (AppTy t1 t2)   = isBaseType t1 && isBaseType t2
isBaseType (FunTy _ _)     = False -- isBaseType t1 && isBaseType t2
isBaseType _               = False

validTyVar :: String -> Bool
validTyVar s@(c:_) = isLower c && all (not . isSpace) s
validTyVar _       = False

tvId α = {- traceShow ("tvId: α = " ++ show α) $ -} showPpr α ++ show (varUnique α)

tracePpr s x = trace ("\nTrace: [" ++ s ++ "] : " ++ showPpr x) x

pprShow = text . show


tidyCBs = map unTick

unTick (NonRec b e) = NonRec b (unTickExpr e)
unTick (Rec bs)     = Rec $ map (second unTickExpr) bs

unTickExpr (App e a)          = App (unTickExpr e) (unTickExpr a)
unTickExpr (Lam b e)          = Lam b (unTickExpr e)
unTickExpr (Let b e)          = Let (unTick b) (unTickExpr e)
unTickExpr (Case e b t as)    = Case (unTickExpr e) b t (map unTickAlt as)
    where unTickAlt (a, b, e) = (a, b, unTickExpr e)
unTickExpr (Cast e c)         = Cast (unTickExpr e) c
unTickExpr (Tick _ e)         = unTickExpr e
unTickExpr x                  = x

isFractionalClass clas = classKey clas `elem` fractionalClassKeys

-----------------------------------------------------------------------
------------------ Generic Helpers for DataConstructors ---------------
-----------------------------------------------------------------------

isDataConId id = case idDetails id of
                  DataConWorkId _ -> True
                  DataConWrapId _ -> True
                  _               -> False

getDataConVarUnique v
  | isId v && isDataConId v = getUnique $ idDataCon v
  | otherwise               = getUnique v


newtype Loc    = L (Int, Int) deriving (Eq, Ord, Show)

instance Hashable Loc where
  hashWithSalt i (L z) = hashWithSalt i z

--instance (Uniquable a) => Hashable a where

instance Hashable SrcSpan where
  hashWithSalt i (UnhelpfulSpan s) = hashWithSalt i (uniq s)
  hashWithSalt i (RealSrcSpan s)   = hashWithSalt i (srcSpanStartLine s, srcSpanStartCol s, srcSpanEndCol s)

instance Outputable a => Outputable (S.HashSet a) where
  ppr = ppr . S.toList

instance ToJSON RealSrcSpan where
  toJSON sp = object [ "filename"  .= f  -- (unpackFS $ srcSpanFile sp)
                     , "startLine" .= l1 -- srcSpanStartLine sp
                     , "startCol"  .= c1 -- srcSpanStartCol  sp
                     , "endLine"   .= l2 -- srcSpanEndLine   sp
                     , "endCol"    .= c2 -- srcSpanEndCol    sp
                     ]
    where
      (f, l1, c1, l2, c2) = unpackRealSrcSpan sp

unpackRealSrcSpan rsp = (f, l1, c1, l2, c2)
  where
    f                 = unpackFS $ srcSpanFile rsp
    l1                = srcSpanStartLine rsp
    c1                = srcSpanStartCol  rsp
    l2                = srcSpanEndLine   rsp
    c2                = srcSpanEndCol    rsp


instance FromJSON RealSrcSpan where
  parseJSON (Object v) = realSrcSpan <$> v .: "filename"
                                     <*> v .: "startLine"
                                     <*> v .: "startCol"
                                     <*> v .: "endLine"
                                     <*> v .: "endCol"
  parseJSON _          = mempty

realSrcSpan f l1 c1 l2 c2 = mkRealSrcSpan loc1 loc2
  where
    loc1                  = mkRealSrcLoc (fsLit f) l1 c1
    loc2                  = mkRealSrcLoc (fsLit f) l2 c2



instance ToJSON SrcSpan where
  toJSON (RealSrcSpan rsp) = object [ "realSpan" .= True, "spanInfo" .= rsp ]
  toJSON (UnhelpfulSpan _) = object [ "realSpan" .= False ]

instance FromJSON SrcSpan where
  parseJSON (Object v) = do tag <- v .: "realSpan"
                            case tag of
                              False -> return noSrcSpan
                              True  -> RealSrcSpan <$> v .: "spanInfo"
  parseJSON _          = mempty


-------------------------------------------------------

toFixSDoc = PJ.text . PJ.render . toFix
sDocDoc   = PJ.text . showSDoc
pprDoc    = sDocDoc . ppr

-- Overriding Outputable functions because they now require DynFlags!
showPpr       = showSDoc . ppr

-- FIXME: somewhere we depend on this printing out all GHC entities with
-- fully-qualified names...
showSDoc sdoc = Out.renderWithStyle unsafeGlobalDynFlags sdoc (Out.mkUserStyle Out.alwaysQualify Out.AllTheWay)
showSDocDump  = Out.showSDocDump unsafeGlobalDynFlags

typeUniqueString = {- ("sort_" ++) . -} showSDocDump . ppr

instance Fixpoint Var where
  toFix = pprDoc

instance Fixpoint Name where
  toFix = pprDoc

instance Fixpoint Type where
  toFix = pprDoc

instance Show Name where
  show = showPpr

instance Show Var where
  show = showPpr

instance Show Class where
  show = showPpr

instance Show TyCon where
  show = showPpr

sourcePosSrcSpan   :: SourcePos -> SrcSpan
sourcePosSrcSpan = srcLocSpan . sourcePosSrcLoc

sourcePosSrcLoc    :: SourcePos -> SrcLoc
sourcePosSrcLoc p = mkSrcLoc (fsLit file) line col
  where
    file          = sourceName p
    line          = sourceLine p
    col           = sourceColumn p

srcSpanSourcePos :: SrcSpan -> SourcePos
srcSpanSourcePos (UnhelpfulSpan _) = dummyPos "LH.GhcMisc.srcSpanSourcePos"
srcSpanSourcePos (RealSrcSpan s)   = realSrcSpanSourcePos s

srcSpanSourcePosE :: SrcSpan -> SourcePos
srcSpanSourcePosE (UnhelpfulSpan _) = dummyPos "LH.GhcMisc.srcSpanSourcePos"
srcSpanSourcePosE (RealSrcSpan s)   = realSrcSpanSourcePosE s



srcSpanFilename    = maybe "" unpackFS . srcSpanFileName_maybe
srcSpanStartLoc l  = L (srcSpanStartLine l, srcSpanStartCol l)
srcSpanEndLoc l    = L (srcSpanEndLine l, srcSpanEndCol l)
oneLine l          = srcSpanStartLine l == srcSpanEndLine l
lineCol l          = (srcSpanStartLine l, srcSpanStartCol l)

realSrcSpanSourcePos :: RealSrcSpan -> SourcePos
realSrcSpanSourcePos s = newPos file line col
  where
    file               = unpackFS $ srcSpanFile s
    line               = srcSpanStartLine       s
    col                = srcSpanStartCol        s


realSrcSpanSourcePosE :: RealSrcSpan -> SourcePos
realSrcSpanSourcePosE s = newPos file line col
  where
    file                = unpackFS $ srcSpanFile s
    line                = srcSpanEndLine       s
    col                 = srcSpanEndCol        s


getSourcePos           = srcSpanSourcePos  . getSrcSpan
getSourcePosE          = srcSpanSourcePosE . getSrcSpan

collectArguments n e = if length xs > n then take n xs else xs
  where (vs', e') = collectValBinders' $ snd $ collectTyBinders e
        vs        = fst $ collectValBinders $ ignoreLetBinds e'
        xs        = vs' ++ vs

collectValBinders' = go []
  where
    go tvs (Lam b e) | isTyVar b = go tvs     e
    go tvs (Lam b e) | isId    b = go (b:tvs) e
    go tvs (Tick _ e)            = go tvs e
    go tvs e                     = (reverse tvs, e)

ignoreLetBinds (Let (NonRec _ _) e')
  = ignoreLetBinds e'
ignoreLetBinds e
  = e

isDictionaryExpression :: Core.Expr Id -> Maybe Id
isDictionaryExpression (Tick _ e) = isDictionaryExpression e
isDictionaryExpression (Var x)    | isDictionary x = Just x
isDictionaryExpression _          = Nothing


realTcArity :: TyCon -> Arity
realTcArity
  = kindArity . TC.tyConKind

kindArity :: Kind -> Arity
kindArity (FunTy _ res)
  = 1 + kindArity res
kindArity (ForAllTy _ res)
  = kindArity res
kindArity _
  = 0


instance Hashable Var where
  hashWithSalt = uniqueHash

instance Hashable TyCon where
  hashWithSalt = uniqueHash

uniqueHash i = hashWithSalt i . getKey . getUnique

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
                        _     -> Out.panic "lookupRdrNameInModule"
                Nothing -> throwCmdLineErrorS dflags $ Out.hsep [Out.ptext (sLit "Could not determine the exports of the module"), ppr mod_name]
        err -> throwCmdLineErrorS dflags $ cannotFindModule dflags mod_name err
  where dflags = hsc_dflags hsc_env
        throwCmdLineErrorS dflags = throwCmdLineError . Out.showSDoc dflags
        throwCmdLineError = throwGhcException . CmdLineError


addContext m = getContext >>= setContext . (m:)

qualImportDecl mn = (simpleImportDecl mn) { ideclQualified = True }

ignoreInline x = x {pm_parsed_source = go <$> pm_parsed_source x}
  where go  x = x {hsmodDecls = filter go' $ hsmodDecls x}
        go' x | SigD (InlineSig _ _) <-  unLoc x = False
              | otherwise                        = True

symbolTyConWithKind k x i n = stringTyConWithKind k x i (symbolString n)
symbolTyCon x i n = stringTyCon x i (symbolString n)
symbolTyVar n = stringTyVar (symbolString n)

instance Symbolic TyCon where
  symbol = symbol . qualifiedNameSymbol . getName

instance Symbolic Name where
  symbol = symbol . showPpr -- qualifiedNameSymbol


instance Symbolic Var where
  symbol = varSymbol

varSymbol ::  Var -> Symbol
varSymbol v
  | us `isSuffixOfSym` vs = vs
  | otherwise             = suffixSymbol vs us
  where
    us                    = symbol $ showPpr $ getDataConVarUnique v
    vs                    = symbol $ getName v

qualifiedNameSymbol n = symbol $
  case nameModule_maybe n of
    Nothing -> occNameFS (getOccName n)
    Just m  -> concatFS [moduleNameFS (moduleName m), fsLit ".", occNameFS (getOccName n)]

instance Symbolic FastString where
  symbol = symbol . fastStringText

fastStringText = T.decodeUtf8 . fastStringToByteString

tyConTyVarsDef c | TC.isPrimTyCon c || isFunTyCon c = []
tyConTyVarsDef c | TC.isPromotedTyCon   c = error ("TyVars on " ++ show c) -- tyConTyVarsDef $ TC.ty_con c
tyConTyVarsDef c | TC.isPromotedDataCon c = error ("TyVars on " ++ show c) -- DC.dataConUnivTyVars $ TC.datacon c
tyConTyVarsDef c = TC.tyConTyVars c



----------------------------------------------------------------------
-- GHC Compatibility Layer
----------------------------------------------------------------------

gHC_VERSION :: String
gHC_VERSION = show __GLASGOW_HASKELL__

symbolFastString :: Symbol -> FastString
symbolFastString = mkFastStringByteString . T.encodeUtf8 . symbolText

desugarModule :: TypecheckedModule -> Ghc DesugaredModule
desugarModule tcm = do
  let ms = pm_mod_summary $ tm_parsed_module tcm
  -- let ms = modSummary tcm
  let (tcg, _) = tm_internals_ tcm
  hsc_env <- getSession
  let hsc_env_tmp = hsc_env { hsc_dflags = ms_hspp_opts ms }
  guts <- liftIO $ hscDesugarWithLoc hsc_env_tmp ms tcg
  return DesugaredModule { dm_typechecked_module = tcm, dm_core_module = guts }

-- desugarModule = GHC.desugarModule

type Prec = TyPrec

lintCoreBindings :: [Var] -> CoreProgram -> (Bag MsgDoc, Bag MsgDoc)
lintCoreBindings = CoreLint.lintCoreBindings CoreDoNothing

synTyConRhs_maybe :: TyCon -> Maybe Type
synTyConRhs_maybe = TC.synTyConRhs_maybe

tcRnLookupRdrName :: HscEnv -> GHC.Located RdrName -> IO (Messages, Maybe [Name])
tcRnLookupRdrName = TcRnDriver.tcRnLookupRdrName


------------------------------------------------------------------------
-- | Manipulating Symbols ----------------------------------------------
------------------------------------------------------------------------

dropModuleNames, takeModuleNames, dropModuleUnique :: Symbol -> Symbol
dropModuleNames  = mungeNames lastName sepModNames "dropModuleNames: "
  where
    lastName msg = symbol . safeLast msg

takeModuleNames  = mungeNames initName sepModNames "takeModuleNames: "
  where
    initName msg = symbol . T.intercalate "." . safeInit msg

dropModuleUnique = mungeNames headName sepUnique   "dropModuleUnique: "
  where
    headName msg = symbol . safeHead msg


sepModNames = "."
sepUnique   = "#"


-- safeHead :: String -> [T.Text] -> Symbol
-- safeHead msg []  = errorstar $ "safeHead with empty list" ++ msg
-- safeHead _ (x:_) = symbol x

-- safeInit :: String -> [T.Text] -> Symbol
-- safeInit _ xs@(_:_)      = symbol $ T.intercalate "." $ init xs
-- safeInit msg _           = errorstar $ "safeInit with empty list " ++ msg

mungeNames :: (String -> [T.Text] -> Symbol) -> T.Text -> String -> Symbol -> Symbol
mungeNames _ _ _ ""  = ""
mungeNames f d msg s'@(symbolText -> s)
  | s' == tupConName = tupConName
  | otherwise        = f (msg ++ T.unpack s) $ T.splitOn d $ stripParens s

qualifySymbol :: Symbol -> Symbol -> Symbol
qualifySymbol (symbolText -> m) x'@(symbolText -> x)
  | isQualified x  = x'
  | isParened x    = symbol (wrapParens (m `mappend` "." `mappend` stripParens x))
  | otherwise      = symbol (m `mappend` "." `mappend` x)

isQualified y = "." `T.isInfixOf` y
wrapParens x  = "(" `mappend` x `mappend` ")"
isParened xs  = xs /= stripParens xs

isDictionary = isPrefixOfSym "$f" . dropModuleNames . symbol
isInternal   = isPrefixOfSym "$"  . dropModuleNames . symbol

stripParens :: T.Text -> T.Text
stripParens t = fromMaybe t (strip t)
  where
    strip = T.stripPrefix "(" >=> T.stripSuffix ")"

stripParensSym :: Symbol -> Symbol
stripParensSym (symbolText -> t) = symbol $ stripParens t

--------------------------------------------------------------------------------
-- | Source Info = Stack of most recent binders/spans
--------------------------------------------------------------------------------
