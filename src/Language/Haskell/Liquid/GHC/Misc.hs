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
{-# LANGUAGE PatternSynonyms           #-}

-- | This module contains a wrappers and utility functions for
-- accessing GHC module information. It should NEVER depend on
-- ANY module inside the Language.Haskell.Liquid.* tree.

module Language.Haskell.Liquid.GHC.Misc where

import           Class                                      (classKey)
import           Data.String
import           PrelNames                                  (fractionalClassKeys)
import           FamInstEnv
import           Debug.Trace

import           DataCon                                    (isTupleDataCon)
import           Prelude                                    hiding (error)
import           Avail                                      (availsToNameSet)
import           BasicTypes                                 (Arity, noOccInfo)
import           CoreSyn                                    hiding (Expr, sourceName)
import qualified CoreSyn                                    as Core
import           CostCentre
import           GHC                                        hiding (L)
import           HscTypes                                   (ModGuts(..), HscEnv(..), FindResult(..),
                                                             Dependencies(..))
import           TysWiredIn                                 (anyTy)
import           NameSet                                    (NameSet)
import           SrcLoc                                     hiding (L)
import           Bag
import           ErrUtils
import           CoreLint
import           CoreMonad

import           Text.Parsec.Pos                            (incSourceColumn, sourceName, sourceLine, sourceColumn, newPos)

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
import           TyCoRep
import           Var
import           IdInfo
import qualified TyCon                                      as TC
import           Data.Char                                  (isLower, isSpace, isUpper)
import           Data.Maybe                                 (isJust, fromMaybe, fromJust)
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
import           Language.Fixpoint.Types                    hiding (L, panic, Loc (..), SrcSpan, Constant, SESearch (..))
import qualified Language.Fixpoint.Types                    as F
import           Language.Fixpoint.Misc                     (safeHead, safeLast, safeInit)
import           Control.DeepSeq
import           Language.Haskell.Liquid.Types.Errors
import           Language.Haskell.Liquid.Desugar.HscMain
import           Id                                         (isExportedId, idOccInfo, setIdInfo)


isAnonBinder :: TC.TyConBinder -> Bool
isAnonBinder (TvBndr _ TC.AnonTCB) = True
isAnonBinder (TvBndr _ _)          = False

mkAlive :: Var -> Id
mkAlive x
  | isId x && isDeadOcc (idOccInfo x)
  = setIdInfo x (setOccInfo (idInfo x) noOccInfo)
  | otherwise
  = x



--------------------------------------------------------------------------------
-- | Datatype For Holding GHC ModGuts ------------------------------------------
--------------------------------------------------------------------------------
data MGIModGuts = MI {
    mgi_binds     :: !CoreProgram
  , mgi_module    :: !Module
  , mgi_deps      :: !Dependencies
  , mgi_dir_imps  :: ![ModuleName]
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
  where _z        = showPpr (zing <$> mg_fam_insts mg)
        zing fi   = (fi_fam fi, fi_tcs fi, fi_tvs fi, fi_rhs fi)

mg_dir_imps :: ModGuts -> [ModuleName]
mg_dir_imps m = fst <$> (dep_mods $ mg_deps m)

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
stringTyCon = stringTyConWithKind anyTy

-- FIXME: reusing uniques like this is really dangerous
stringTyConWithKind :: Kind -> Char -> Int -> String -> TyCon
stringTyConWithKind k c n s = TC.mkKindTyCon name [] k [] name
  where
    name          = mkInternalName (mkUnique c n) occ noSrcSpan
    occ           = mkTcOcc s

hasBaseTypeVar :: Var -> Bool
hasBaseTypeVar = isBaseType . varType

-- same as Constraint isBase
isBaseType :: Type -> Bool
isBaseType (ForAllTy _ _)  = False
isBaseType (FunTy t1 t2)   = isBaseType t1 && isBaseType t2
isBaseType (TyVarTy _)     = True
isBaseType (TyConApp _ ts) = all isBaseType ts
isBaseType (AppTy t1 t2)   = isBaseType t1 && isBaseType t2
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
showSDoc sdoc = Out.renderWithStyle unsafeGlobalDynFlags sdoc (Out.mkUserStyle unsafeGlobalDynFlags myQualify {- Out.alwaysQualify -} Out.AllTheWay)

myQualify :: Out.PrintUnqualified
myQualify = Out.neverQualify { Out.queryQualifyName = Out.alwaysQualifyNames }
-- { Out.queryQualifyName = \_ _ -> Out.NameNotInScope1 }

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
sourcePosSrcSpan p = sourcePos2SrcSpan p (incSourceColumn p 1)

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
getSourcePos = srcSpanSourcePos  . getSrcSpan

getSourcePosE :: NamedThing a => a -> SourcePos
getSourcePosE = srcSpanSourcePosE . getSrcSpan

locNamedThing :: NamedThing a => a -> F.Located a
locNamedThing x = F.Loc l lE x
  where
    l          = getSourcePos  x
    lE         = getSourcePosE x

namedLocSymbol :: (F.Symbolic a, NamedThing a) => a -> F.Located F.Symbol
namedLocSymbol d = {- dropModuleNamesAndUnique . -} F.symbol <$> locNamedThing d

varLocInfo :: (Type -> a) -> Var -> F.Located a
varLocInfo f x = f . varType <$> locNamedThing x

namedPanic :: (NamedThing a) => a -> String -> b
namedPanic x msg = panic (Just (getSrcSpan x)) msg

--------------------------------------------------------------------------------
-- | Manipulating CoreExpr -----------------------------------------------------
--------------------------------------------------------------------------------

collectArguments :: Int -> CoreExpr -> [Var]
collectArguments n e = if length xs > n then take n xs else xs
  where
    (vs', e')        = collectValBinders' $ snd $ collectTyBinders e
    vs               = fst $ collectBinders $ ignoreLetBinds e'
    xs               = vs' ++ vs

{-
collectTyBinders :: CoreExpr -> ([Var], CoreExpr)
collectTyBinders expr
  = go [] expr
  where
    go tvs (Lam b e) | isTyVar b = go (b:tvs) e
    go tvs e                     = (reverse tvs, e)
-}

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
realTcArity = tyConArity

{-
  tracePpr ("realTcArity of " ++ showPpr c
     ++ "\n tyConKind = " ++ showPpr (tyConKind c)
     ++ "\n kindArity = " ++ show (kindArity (tyConKind c))
     ++ "\n kindArity' = " ++ show (kindArity' (tyConKind c)) -- this works for TypeAlias
     ) $ kindArity' (tyConKind c)
-}

kindTCArity :: TyCon -> Arity
kindTCArity = go . tyConKind
  where
    go (FunTy _ res) = 1 + go res
    go _             = 0


kindArity :: Kind -> Arity
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
                        provenance = Just $ ImpSpec decl_spec ImpAll
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


localVarSymbol ::  Var -> Symbol
localVarSymbol v
  | us `isSuffixOfSym` vs = vs
  | otherwise             = suffixSymbol vs us
  where
    us                    = symbol $ showPpr $ getDataConVarUnique v
    vs                    = exportedVarSymbol v -- TODO:reflect-datacons varSymbol

exportedVarSymbol :: Var -> Symbol
exportedVarSymbol = symbol . getName            -- TODO:reflect-datacons varSymbol

qualifiedNameSymbol :: Name -> Symbol
qualifiedNameSymbol n = symbol $ concatFS [modFS, occFS, uniqFS]
  where
  _msg   = showSDoc (ppr n) -- getOccString n
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
tyConTyVarsDef c
  | noTyVars c = []
  | otherwise  = TC.tyConTyVars c
  --where
  --  none         = tracepp ("tyConTyVarsDef: " ++ show c) (noTyVars c)

noTyVars :: TyCon -> Bool
noTyVars c =  (TC.isPrimTyCon c || isFunTyCon c || TC.isPromotedDataCon c)

--------------------------------------------------------------------------------
-- | Symbol Instances
--------------------------------------------------------------------------------

instance Symbolic TyCon where
  symbol = symbol . getName

instance Symbolic Class where
  symbol = symbol . getName

instance Symbolic Name where
  symbol = symbol . qualifiedNameSymbol

-- | [NOTE:REFLECT-IMPORTS] we **eschew** the `unique` suffix for exported vars,
-- to make it possible to lookup names from symbols _across_ modules;
-- anyways exported names are top-level and you shouldn't have local binders
-- that shadow them. However, we **keep** the `unique` suffix for local variables,
-- as otherwise there are spurious, but extremely problematic, name collisions
-- in the fixpoint environment.

instance Symbolic Var where   -- TODO:reflect-datacons varSymbol
  symbol v
    | isExportedId v = exportedVarSymbol v
    | otherwise      = localVarSymbol    v

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

instance NFData TyCon where
  rnf t = seq t ()

instance NFData Type where
  rnf t = seq t ()

instance NFData Var where
  rnf t = seq t ()


--------------------------------------------------------------------------------
-- | Manipulating Symbols ------------------------------------------------------
--------------------------------------------------------------------------------

splitModuleName :: Symbol -> (Symbol, Symbol)
splitModuleName x = (takeModuleNames x, dropModuleNamesAndUnique x)

dropModuleNamesAndUnique :: Symbol -> Symbol
dropModuleNamesAndUnique = dropModuleUnique . dropModuleNames

dropModuleNames  :: Symbol -> Symbol
dropModuleNames = mungeNames lastName sepModNames "dropModuleNames: "
 where
   lastName msg = symbol . safeLast msg

dropModuleNamesCorrect  :: Symbol -> Symbol
dropModuleNamesCorrect = F.symbol . go . F.symbolText
  where
    go s = case T.uncons s of
             Just (c,tl) -> if isUpper c  && T.any (== '.') tl
                              then go $ snd $ fromJust $ T.uncons $ T.dropWhile (/= '.') s
                              else s
             Nothing -> s

takeModuleNames  :: Symbol -> Symbol
takeModuleNames  = mungeNames initName sepModNames "takeModuleNames: "
  where
    initName msg = symbol . T.intercalate "." . safeInit msg

dropModuleUnique :: Symbol -> Symbol
dropModuleUnique = mungeNames headName sepUnique   "dropModuleUnique: "
  where
    headName msg = symbol . safeHead msg


cmpSymbol :: Symbol -> Symbol -> Bool
cmpSymbol coreSym logicSym
  =  (dropModuleUnique coreSym == dropModuleNamesAndUnique logicSym)
  || (dropModuleUnique coreSym == dropModuleUnique         logicSym)

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

desugarModule :: TypecheckedModule -> Ghc DesugaredModule
desugarModule tcm = do
  let ms = pm_mod_summary $ tm_parsed_module tcm
  -- let ms = modSummary tcm
  let (tcg, _) = tm_internals_ tcm
  hsc_env <- getSession
  let hsc_env_tmp = hsc_env { hsc_dflags = ms_hspp_opts ms }
  guts <- liftIO $ hscDesugarWithLoc hsc_env_tmp ms tcg
  return DesugaredModule { dm_typechecked_module = tcm, dm_core_module = guts }

--------------------------------------------------------------------------------
-- | GHC Compatibility Layer ---------------------------------------------------
--------------------------------------------------------------------------------

gHC_VERSION :: String
gHC_VERSION = show __GLASGOW_HASKELL__

symbolFastString :: Symbol -> FastString
symbolFastString = mkFastStringByteString . T.encodeUtf8 . symbolText

type Prec = TyPrec

lintCoreBindings :: [Var] -> CoreProgram -> (Bag MsgDoc, Bag MsgDoc)
lintCoreBindings = CoreLint.lintCoreBindings (defaultDynFlags undefined) CoreDoNothing

synTyConRhs_maybe :: TyCon -> Maybe Type
synTyConRhs_maybe = TC.synTyConRhs_maybe

tcRnLookupRdrName :: HscEnv -> GHC.Located RdrName -> IO (Messages, Maybe [Name])
tcRnLookupRdrName = TcRnDriver.tcRnLookupRdrName

showCBs :: Bool -> [CoreBind] -> String
showCBs untidy
  | untidy    = Out.showSDocDebug unsafeGlobalDynFlags . ppr . tidyCBs
  | otherwise = showPpr

findVarDef :: Symbol -> [CoreBind] -> Maybe (Var, CoreExpr)
findVarDef x cbs = case xCbs of
                     (NonRec v def   : _ ) -> Just (v, def)
                     (Rec [(v, def)] : _ ) -> Just (v, def)
                     _                     -> Nothing
  where
    xCbs            = [ cb | cb <- concatMap unRec cbs, x `elem` coreBindSymbols cb ]
    unRec (Rec xes) = [NonRec x es | (x,es) <- xes]
    unRec nonRec    = [nonRec]


coreBindSymbols :: CoreBind -> [Symbol]
coreBindSymbols = map (dropModuleNames . simplesymbol) . binders

simplesymbol :: (NamedThing t) => t -> Symbol
simplesymbol = symbol . getName

binders :: Bind a -> [a]
binders (NonRec z _) = [z]
binders (Rec xes)    = fst <$> xes
