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

import           Class                                      (classKey)
import           Data.String
import           PrelNames                                  (fractionalClassKeys)

import           Debug.Trace

import           DataCon                                    (isTupleDataCon)
import           Prelude                                    hiding (error)
import           Avail                                      (availsToNameSet)
import           BasicTypes                                 (Arity)
import           CoreSyn                                    hiding (Expr, sourceName)
import qualified CoreSyn                                    as Core
import           CostCentre
import           GHC                                        hiding (L)
import           HscTypes                                   (Dependencies, ImportedMods, ModGuts(..), HscEnv(..), FindResult(..))
import           Kind                                       (superKind)
import           NameSet                                    (NameSet)
import           SrcLoc                                     hiding (L)
import           Bag
import           ErrUtils
import           CoreLint
import           CoreMonad

import           Text.Parsec.Pos                            (sourceName, sourceLine, sourceColumn, newPos)

import           Name
import           Module                                     (moduleNameFS)
import           Unique
import           Finder                                     (findImportedModule, cannotFindModule)
import           Panic                                      (throwGhcException)
import           FastString
import           TcRnDriver
-- import           TcRnTypes


import           RdrName
import           Type                                       (liftedTypeKind)
import           TypeRep
import           Var
import           IdInfo
import qualified TyCon                                      as TC
import           Data.Char                                  (isLower, isSpace)
import           Data.Maybe                                 (isJust, fromMaybe)
import           Data.Hashable
import qualified Data.HashSet                               as S

import qualified Data.Text.Encoding.Error                   as TE
import qualified Data.Text.Encoding                         as T
import qualified Data.Text                                  as T
import           Control.Arrow                              (second)
import           Control.Monad                              ((>=>))
import           Outputable                                 (Outputable (..), text, ppr)
import qualified Outputable                                 as Out
import           DynFlags
import qualified Text.PrettyPrint.HughesPJ                  as PJ
import           Language.Fixpoint.Types                    hiding (L, Loc (..), SrcSpan, Constant, SESearch (..))
import qualified Language.Fixpoint.Types                    as F
import           Language.Fixpoint.Misc                     (safeHead, safeLast, safeInit)
import           Language.Haskell.Liquid.Desugar.HscMain
import           Control.DeepSeq
import           Language.Haskell.Liquid.Types.Errors

--------------------------------------------------------------------------------
-- | Datatype For Holding GHC ModGuts ------------------------------------------
--------------------------------------------------------------------------------
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

miModGuts :: Maybe [ClsInst] -> ModGuts -> MGIModGuts
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

mgi_namestring :: MGIModGuts -> String
mgi_namestring = moduleNameString . moduleName . mgi_module

--------------------------------------------------------------------------------
-- | Encoding and Decoding Location --------------------------------------------
--------------------------------------------------------------------------------
srcSpanTick :: Module -> SrcSpan -> Tickish a
srcSpanTick m sp = ProfNote (AllCafsCC m sp) False True

tickSrcSpan ::  Outputable a => Tickish a -> SrcSpan
tickSrcSpan (ProfNote cc _ _) = cc_loc cc
tickSrcSpan (SourceNote ss _) = RealSrcSpan ss
tickSrcSpan _                 = noSrcSpan

--------------------------------------------------------------------------------
-- | Generic Helpers for Accessing GHC Innards ---------------------------------
--------------------------------------------------------------------------------

-- FIXME: reusing uniques like this is really dangerous
stringTyVar :: String -> TyVar
stringTyVar s = mkTyVar name liftedTypeKind
  where name = mkInternalName (mkUnique 'x' 24)  occ noSrcSpan
        occ  = mkTyVarOcc s

-- FIXME: reusing uniques like this is really dangerous
stringVar :: String -> Type -> Var
stringVar s t = mkLocalVar VanillaId name t vanillaIdInfo
   where
      name = mkInternalName (mkUnique 'x' 25) occ noSrcSpan
      occ  = mkVarOcc s

stringTyCon :: Char -> Int -> String -> TyCon
stringTyCon = stringTyConWithKind superKind

-- FIXME: reusing uniques like this is really dangerous
stringTyConWithKind :: Kind -> Char -> Int -> String -> TyCon
stringTyConWithKind k c n s = TC.mkKindTyCon name k
  where
    name          = mkInternalName (mkUnique c n) occ noSrcSpan
    occ           = mkTcOcc s

hasBaseTypeVar :: Var -> Bool
hasBaseTypeVar = isBaseType . varType

-- same as Constraint isBase
isBaseType :: Type -> Bool
isBaseType (ForAllTy _ t)  = isBaseType t
isBaseType (TyVarTy _)     = True
isBaseType (TyConApp _ ts) = all isBaseType ts
isBaseType (AppTy t1 t2)   = isBaseType t1 && isBaseType t2
isBaseType (FunTy _ _)     = False -- isBaseType t1 && isBaseType t2
isBaseType _               = False

validTyVar :: String -> Bool
validTyVar s@(c:_) = isLower c && all (not . isSpace) s
validTyVar _       = False

tvId :: TyVar -> String
tvId α = {- traceShow ("tvId: α = " ++ show α) $ -} showPpr α ++ show (varUnique α)

tidyCBs :: [CoreBind] -> [CoreBind]
tidyCBs = map unTick

unTick :: CoreBind -> CoreBind
unTick (NonRec b e) = NonRec b (unTickExpr e)
unTick (Rec bs)     = Rec $ map (second unTickExpr) bs

unTickExpr :: CoreExpr -> CoreExpr
unTickExpr (App e a)          = App (unTickExpr e) (unTickExpr a)
unTickExpr (Lam b e)          = Lam b (unTickExpr e)
unTickExpr (Let b e)          = Let (unTick b) (unTickExpr e)
unTickExpr (Case e b t as)    = Case (unTickExpr e) b t (map unTickAlt as)
    where unTickAlt (a, b, e) = (a, b, unTickExpr e)
unTickExpr (Cast e c)         = Cast (unTickExpr e) c
unTickExpr (Tick _ e)         = unTickExpr e
unTickExpr x                  = x

isFractionalClass :: Class -> Bool
isFractionalClass clas = classKey clas `elem` fractionalClassKeys


--------------------------------------------------------------------------------
-- | Pretty Printers -----------------------------------------------------------
--------------------------------------------------------------------------------

tracePpr :: Outputable a => String -> a -> a
tracePpr s x = trace ("\nTrace: [" ++ s ++ "] : " ++ showPpr x) x

pprShow :: Show a => a -> Out.SDoc
pprShow = text . show


toFixSDoc :: Fixpoint a => a -> PJ.Doc
toFixSDoc = PJ.text . PJ.render . toFix

sDocDoc :: Out.SDoc -> PJ.Doc
sDocDoc   = PJ.text . showSDoc

pprDoc :: Outputable a => a -> PJ.Doc
pprDoc    = sDocDoc . ppr

-- Overriding Outputable functions because they now require DynFlags!
showPpr :: Outputable a => a -> String
showPpr       = showSDoc . ppr

-- FIXME: somewhere we depend on this printing out all GHC entities with
-- fully-qualified names...
showSDoc :: Out.SDoc -> String
showSDoc sdoc = Out.renderWithStyle unsafeGlobalDynFlags sdoc (Out.mkUserStyle Out.alwaysQualify Out.AllTheWay)

showSDocDump :: Out.SDoc -> String
showSDocDump  = Out.showSDocDump unsafeGlobalDynFlags

instance Outputable a => Outputable (S.HashSet a) where
  ppr = ppr . S.toList

typeUniqueString :: Outputable a => a -> String
typeUniqueString = {- ("sort_" ++) . -} showSDocDump . ppr


--------------------------------------------------------------------------------
-- | Manipulating Source Spans -------------------------------------------------
--------------------------------------------------------------------------------

newtype Loc    = L (Int, Int) deriving (Eq, Ord, Show)

instance Hashable Loc where
  hashWithSalt i (L z) = hashWithSalt i z

--instance (Uniquable a) => Hashable a where

instance Hashable SrcSpan where
  hashWithSalt i (UnhelpfulSpan s) = hashWithSalt i (uniq s)
  hashWithSalt i (RealSrcSpan s)   = hashWithSalt i (srcSpanStartLine s, srcSpanStartCol s, srcSpanEndCol s)
fSrcSpan :: (F.Loc a) => a -> SrcSpan
fSrcSpan = fSrcSpanSrcSpan . F.srcSpan

fSrcSpanSrcSpan :: F.SrcSpan -> SrcSpan
fSrcSpanSrcSpan (F.SS p p') = sourcePos2SrcSpan p p'

srcSpanFSrcSpan :: SrcSpan -> F.SrcSpan
srcSpanFSrcSpan sp = F.SS p p'
  where
    p              = srcSpanSourcePos sp
    p'             = srcSpanSourcePosE sp

sourcePos2SrcSpan :: SourcePos -> SourcePos -> SrcSpan
sourcePos2SrcSpan p p' = RealSrcSpan $ realSrcSpan f l c l' c'
  where
    (f, l,  c)         = F.sourcePosElts p
    (_, l', c')        = F.sourcePosElts p'

sourcePosSrcSpan   :: SourcePos -> SrcSpan
sourcePosSrcSpan = srcLocSpan . sourcePosSrcLoc

sourcePosSrcLoc    :: SourcePos -> SrcLoc
sourcePosSrcLoc p = mkSrcLoc (fsLit file) line col
  where
    file          = sourceName p
    line          = sourceLine p
    col           = sourceColumn p

srcSpanSourcePos :: SrcSpan -> SourcePos
srcSpanSourcePos (UnhelpfulSpan _) = dummyPos "<no source information>"
srcSpanSourcePos (RealSrcSpan s)   = realSrcSpanSourcePos s

srcSpanSourcePosE :: SrcSpan -> SourcePos
srcSpanSourcePosE (UnhelpfulSpan _) = dummyPos "<no source information>"
srcSpanSourcePosE (RealSrcSpan s)   = realSrcSpanSourcePosE s

srcSpanFilename :: SrcSpan -> String
srcSpanFilename    = maybe "" unpackFS . srcSpanFileName_maybe

srcSpanStartLoc :: RealSrcSpan -> Loc
srcSpanStartLoc l  = L (srcSpanStartLine l, srcSpanStartCol l)

srcSpanEndLoc :: RealSrcSpan -> Loc
srcSpanEndLoc l    = L (srcSpanEndLine l, srcSpanEndCol l)

oneLine :: RealSrcSpan -> Bool
oneLine l          = srcSpanStartLine l == srcSpanEndLine l

lineCol :: RealSrcSpan -> (Int, Int)
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


getSourcePos :: NamedThing a => a -> SourcePos
getSourcePos           = srcSpanSourcePos  . getSrcSpan

getSourcePosE :: NamedThing a => a -> SourcePos
getSourcePosE          = srcSpanSourcePosE . getSrcSpan


--------------------------------------------------------------------------------
-- | Manipulating CoreExpr -----------------------------------------------------
--------------------------------------------------------------------------------

collectArguments :: Int -> CoreExpr -> [Var]
collectArguments n e = if length xs > n then take n xs else xs
  where
    (vs', e')        = collectValBinders' $ snd $ collectTyBinders e
    vs               = fst $ collectValBinders $ ignoreLetBinds e'
    xs               = vs' ++ vs

collectValBinders' :: Core.Expr Var -> ([Var], Core.Expr Var)
collectValBinders' = go []
  where
    go tvs (Lam b e) | isTyVar b = go tvs     e
    go tvs (Lam b e) | isId    b = go (b:tvs) e
    go tvs (Tick _ e)            = go tvs e
    go tvs e                     = (reverse tvs, e)

ignoreLetBinds :: Core.Expr t -> Core.Expr t
ignoreLetBinds (Let (NonRec _ _) e')
  = ignoreLetBinds e'
ignoreLetBinds e
  = e

--------------------------------------------------------------------------------
-- | Predicates on CoreExpr and DataCons ---------------------------------------
--------------------------------------------------------------------------------

isTupleId :: Id -> Bool
isTupleId = maybe False isTupleDataCon . idDataConM

idDataConM :: Id -> Maybe DataCon
idDataConM x = case idDetails x of
  DataConWorkId d -> Just d
  DataConWrapId d -> Just d
  _               -> Nothing

isDataConId :: Id -> Bool
isDataConId = isJust . idDataConM

getDataConVarUnique :: Var -> Unique
getDataConVarUnique v
  | isId v && isDataConId v = getUnique $ idDataCon v
  | otherwise               = getUnique v

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
  = 1 + kindArity res
kindArity _
  = 0

uniqueHash :: Uniquable a => Int -> a -> Int
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


qualImportDecl :: ModuleName -> ImportDecl name
qualImportDecl mn = (simpleImportDecl mn) { ideclQualified = True }

ignoreInline :: ParsedModule -> ParsedModule
ignoreInline x = x {pm_parsed_source = go <$> pm_parsed_source x}
  where go  x = x {hsmodDecls = filter go' $ hsmodDecls x}
        go' x | SigD (InlineSig _ _) <-  unLoc x = False
              | otherwise                        = True

--------------------------------------------------------------------------------
-- | Symbol Conversions --------------------------------------------------------
--------------------------------------------------------------------------------

symbolTyConWithKind :: Kind -> Char -> Int -> Symbol -> TyCon
symbolTyConWithKind k x i n = stringTyConWithKind k x i (symbolString n)

symbolTyCon :: Char -> Int -> Symbol -> TyCon
symbolTyCon x i n = stringTyCon x i (symbolString n)

symbolTyVar :: Symbol -> TyVar
symbolTyVar n = stringTyVar (symbolString n)

varSymbol ::  Var -> Symbol
varSymbol v
  | us `isSuffixOfSym` vs = vs
  | otherwise             = suffixSymbol vs us
  where
    us                    = symbol $ showPpr $ getDataConVarUnique v
    vs                    = symbol $ getName v

qualifiedNameSymbol :: Name -> Symbol
qualifiedNameSymbol n = symbol $ concatFS [modFS, occFS, uniqFS]
  where
  modFS = case nameModule_maybe n of
            Nothing -> fsLit ""
            Just m  -> concatFS [moduleNameFS (moduleName m), fsLit "."]
  occFS = occNameFS (getOccName n)
  uniqFS
    | isSystemName n
    = concatFS [fsLit "_",  fsLit (showPpr (getUnique n))]
    | otherwise
    = fsLit ""

instance Symbolic FastString where
  symbol = symbol . fastStringText

fastStringText :: FastString -> T.Text
fastStringText = T.decodeUtf8With TE.lenientDecode . fastStringToByteString

tyConTyVarsDef :: TyCon -> [TyVar]
tyConTyVarsDef c | TC.isPrimTyCon c || isFunTyCon c = []
tyConTyVarsDef c | TC.isPromotedTyCon   c = []
tyConTyVarsDef c | TC.isPromotedDataCon c = []
tyConTyVarsDef c = TC.tyConTyVars c

--------------------------------------------------------------------------------
-- | Symbol Instances
--------------------------------------------------------------------------------

instance Symbolic TyCon where
  symbol = symbol . getName

instance Symbolic Class where
  symbol = symbol . getName

instance Symbolic Name where
  symbol = symbol . qualifiedNameSymbol

instance Symbolic Var where
  symbol = varSymbol

instance Hashable Var where
  hashWithSalt = uniqueHash

instance Hashable TyCon where
  hashWithSalt = uniqueHash

instance Fixpoint Var where
  toFix = pprDoc

instance Fixpoint Name where
  toFix = pprDoc

instance Fixpoint Type where
  toFix = pprDoc

instance Show Name where
  show = symbolString . symbol

instance Show Var where
  show = show . getName

instance Show Class where
  show = show . getName

instance Show TyCon where
  show = show . getName

instance NFData Class where
  rnf t = seq t ()

instance NFData SrcSpan where
  rnf t = seq t ()

instance NFData TyCon where
  rnf t = seq t ()

instance NFData Type where
  rnf t = seq t ()

instance NFData Var where
  rnf t = seq t ()


--------------------------------------------------------------------------------
-- | Manipulating Symbols ------------------------------------------------------
--------------------------------------------------------------------------------

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

sepModNames :: T.Text
sepModNames = "."

sepUnique :: T.Text
sepUnique = "#"

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

isQualified :: T.Text -> Bool
isQualified y = "." `T.isInfixOf` y

wrapParens :: (IsString a, Monoid a) => a -> a
wrapParens x  = "(" `mappend` x `mappend` ")"

isParened :: T.Text -> Bool
isParened xs  = xs /= stripParens xs

isDictionary :: Symbolic a => a -> Bool
isDictionary = isPrefixOfSym "$f" . dropModuleNames . symbol

isInternal :: Symbolic a => a -> Bool
isInternal   = isPrefixOfSym "$"  . dropModuleNames . symbol

stripParens :: T.Text -> T.Text
stripParens t = fromMaybe t (strip t)
  where
    strip = T.stripPrefix "(" >=> T.stripSuffix ")"

stripParensSym :: Symbol -> Symbol
stripParensSym (symbolText -> t) = symbol $ stripParens t



--------------------------------------------------------------------------------
-- | GHC Compatibility Layer ---------------------------------------------------
--------------------------------------------------------------------------------

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

showCBs :: Bool -> [CoreBind] -> String
showCBs untidy
  | untidy    = Out.showSDocDebug unsafeGlobalDynFlags . ppr . tidyCBs
  | otherwise = showPpr
