{-# LANGUAGE CPP                       #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE MagicHash                 #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE ViewPatterns              #-}
{-# LANGUAGE PatternSynonyms           #-}

{-# OPTIONS_GHC -Wno-incomplete-patterns #-} -- TODO(#1918): Only needed for GHC <9.0.1.
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-x-partial #-}

-- | This module contains a wrappers and utility functions for
-- accessing GHC module information. It should NEVER depend on
-- ANY module inside the Language.Haskell.Liquid.* tree.

module  Language.Haskell.Liquid.GHC.Misc where

import           Data.String
import qualified Data.List as L
import           Data.Word (Word64)
import           Debug.Trace

import           Prelude                                    hiding (error)
import           Liquid.GHC.API            as Ghc hiding
  (L, line, sourceName, showPpr, panic, showSDoc)
import qualified Liquid.GHC.API            as Ghc (GenLocated (L))


import           Data.Char                                  (isLower, isSpace, isUpper)
import           Data.Maybe                                 (isJust, fromMaybe, fromJust, maybeToList)
import           Data.Hashable
import qualified Data.HashSet                               as S
import qualified Data.Map.Strict                            as OM
import           Control.Monad.State                        (evalState, get, modify)

import qualified Data.Text.Encoding.Error                   as TE
import qualified Data.Text.Encoding                         as T
import qualified Data.Text                                  as T
import           Control.Arrow                              (second)
import           Control.Monad                              ((>=>), foldM, when)
import qualified Text.PrettyPrint.HughesPJ                  as PJ
import           Language.Fixpoint.Types                    hiding (L, panic, Loc (..), SrcSpan, Constant, SESearch (..))
import qualified Language.Fixpoint.Types                    as F
import           Language.Fixpoint.Misc                     (safeHead, safeLast, errorstar) -- , safeLast, safeInit)
import           Language.Haskell.Liquid.Misc               (keyDiff)
import           Control.DeepSeq
import           Language.Haskell.Liquid.Types.Errors


isAnonBinder :: Ghc.TyConBinder -> Bool
isAnonBinder (Bndr _ AnonTCB) = True
isAnonBinder (Bndr _ _)           = False

mkAlive :: Var -> Id
mkAlive x
  | isId x && isDeadOcc (idOccInfo x)
  = setIdInfo x (setOccInfo (idInfo x) noOccInfo)
  | otherwise
  = x


--------------------------------------------------------------------------------
-- | Encoding and Decoding Location --------------------------------------------
--------------------------------------------------------------------------------

tickSrcSpan :: CoreTickish -> SrcSpan
tickSrcSpan (ProfNote cc _ _) = cc_loc cc
tickSrcSpan (SourceNote ss _) = RealSrcSpan ss strictNothing
tickSrcSpan _                 = noSrcSpan

--------------------------------------------------------------------------------
-- | Generic Helpers for Accessing GHC Innards ---------------------------------
--------------------------------------------------------------------------------

-- FIXME: reusing uniques like this is really dangerous
stringTyVar :: String -> TyVar
stringTyVar s = mkTyVar name liftedTypeKind
  where
    name      = mkInternalName (mkUnique 'x' 24)  occ noSrcSpan
    occ       = mkTyVarOcc s

-- FIXME: reusing uniques like this is really dangerous
stringVar :: String -> Type -> Var
stringVar s t = mkLocalVar VanillaId name ManyTy t vanillaIdInfo
   where
      name = mkInternalName (mkUnique 'x' 25) occ noSrcSpan
      occ  = mkVarOcc s

-- FIXME: plugging in dummy type like this is really dangerous
maybeAuxVar :: Symbol -> Maybe Var
maybeAuxVar s
  | isMethod sym = Just sv
  | otherwise = Nothing
  where (_, uid) = splitModuleUnique s
        sym = dropModuleNames s
        sv = mkExportedLocalId VanillaId name anyTy
        -- 'x' is chosen for no particular reason..
        name = mkInternalName (mkUnique 'x' uid) occ noSrcSpan
        occ = mkVarOcc (T.unpack (symbolText sym))

stringTyCon :: Char -> Word64 -> String -> TyCon
stringTyCon = stringTyConWithKind anyTy

-- FIXME: reusing uniques like this is really dangerous
stringTyConWithKind :: Kind -> Char -> Word64 -> String -> TyCon
stringTyConWithKind k c n s = Ghc.mkPrimTyCon name [] k []
  where
    name          = mkInternalName (mkUnique c n) occ noSrcSpan
    occ           = mkTcOcc s

hasBaseTypeVar :: Var -> Bool
hasBaseTypeVar = isBaseType . varType

-- same as Constraint isBase
isBaseType :: Type -> Bool
isBaseType (ForAllTy _ _)  = False
isBaseType (FunTy { ft_arg = t1, ft_res = t2}) = isBaseType t1 && isBaseType t2
isBaseType (TyVarTy _)     = True
isBaseType (TyConApp _ ts) = all isBaseType ts
isBaseType (AppTy t1 t2)   = isBaseType t1 && isBaseType t2
isBaseType _               = False

isTmpVar :: Var -> Bool
isTmpVar = isTmpSymbol . dropModuleNamesAndUnique . symbol

isTmpSymbol    :: Symbol -> Bool
isTmpSymbol x  = any (`isPrefixOfSym` x) [anfPrefix, tempPrefix, "ds_"]

validTyVar :: String -> Bool
validTyVar s@(c:_) = isLower c && not (any isSpace s)
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
  where unTickAlt (Alt a b' e') = Alt a b' (unTickExpr e')
unTickExpr (Cast e c)         = Cast (unTickExpr e) c
unTickExpr (Tick _ e)         = unTickExpr e
unTickExpr x                  = x

isFractionalClass :: Class -> Bool
isFractionalClass clas = classKey clas `elem` fractionalClassKeys

isOrdClass :: Class -> Bool
isOrdClass clas = classKey clas == ordClassKey

--------------------------------------------------------------------------------
-- | Pretty Printers -----------------------------------------------------------
--------------------------------------------------------------------------------
notracePpr :: Outputable a => String -> a -> a
notracePpr _ x = x

tracePpr :: Outputable a => String -> a -> a
tracePpr s x = trace ("\nTrace: [" ++ s ++ "] : " ++ showPpr x) x

pprShow :: Show a => a -> Ghc.SDoc
pprShow = text . show


toFixSDoc :: Fixpoint a => a -> PJ.Doc
toFixSDoc = PJ.text . PJ.render . toFix

sDocDoc :: Ghc.SDoc -> PJ.Doc
sDocDoc   = PJ.text . showSDoc

pprDoc :: Outputable a => a -> PJ.Doc
pprDoc    = sDocDoc . ppr

-- Overriding Outputable functions because they now require DynFlags!
showPpr :: Outputable a => a -> String
showPpr = Ghc.showPprQualified

-- FIXME: somewhere we depend on this printing out all GHC entities with
-- fully-qualified names...
showSDoc :: Ghc.SDoc -> String
showSDoc = Ghc.showSDocQualified

myQualify :: Ghc.NamePprCtx
myQualify = Ghc.neverQualify { Ghc.queryQualifyName = Ghc.alwaysQualifyNames }
-- { Ghc.queryQualifyName = \_ _ -> Ghc.NameNotInScope1 }

showSDocDump :: Ghc.SDoc -> String
showSDocDump  = Ghc.renderWithContext Ghc.defaultSDocContext

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
  hashWithSalt i (UnhelpfulSpan reason) = case reason of
    UnhelpfulNoLocationInfo -> hashWithSalt i (uniq $ fsLit "UnhelpfulNoLocationInfo")
    UnhelpfulWiredIn        -> hashWithSalt i (uniq $ fsLit "UnhelpfulWiredIn")
    UnhelpfulInteractive    -> hashWithSalt i (uniq $ fsLit "UnhelpfulInteractive")
    UnhelpfulGenerated      -> hashWithSalt i (uniq $ fsLit "UnhelpfulGenerated")
    UnhelpfulOther fs       -> hashWithSalt i (uniq fs)
  hashWithSalt i (RealSrcSpan s _)      = hashWithSalt i (srcSpanStartLine s, srcSpanStartCol s, srcSpanEndCol s)

fSrcSpan :: (F.Loc a) => a -> SrcSpan
fSrcSpan = fSrcSpanSrcSpan . F.srcSpan

fSourcePos :: (F.Loc a) => a -> F.SourcePos
fSourcePos = F.sp_start . F.srcSpan

fSrcSpanSrcSpan :: F.SrcSpan -> SrcSpan
fSrcSpanSrcSpan (F.SS p p') = sourcePos2SrcSpan p p'

srcSpanFSrcSpan :: SrcSpan -> F.SrcSpan
srcSpanFSrcSpan sp = F.SS p p'
  where
    p              = srcSpanSourcePos sp
    p'             = srcSpanSourcePosE sp

sourcePos2SrcSpan :: SourcePos -> SourcePos -> SrcSpan
sourcePos2SrcSpan p p' = RealSrcSpan (packRealSrcSpan f (unPos l) (unPos c) (unPos l') (unPos c')) strictNothing
  where
    (f, l,  c)         = F.sourcePosElts p
    (_, l', c')        = F.sourcePosElts p'

sourcePosSrcSpan   :: SourcePos -> SrcSpan
sourcePosSrcSpan p@(SourcePos file line col) = sourcePos2SrcSpan p (SourcePos file line (succPos col))

sourcePosSrcLoc    :: SourcePos -> SrcLoc
sourcePosSrcLoc (SourcePos file line col) = mkSrcLoc (fsLit file) (unPos line) (unPos col)

srcSpanSourcePos :: SrcSpan -> SourcePos
srcSpanSourcePos (UnhelpfulSpan _) = dummyPos "<no source information>"
srcSpanSourcePos (RealSrcSpan s _) = realSrcSpanSourcePos s

srcSpanSourcePosE :: SrcSpan -> SourcePos
srcSpanSourcePosE (UnhelpfulSpan _) = dummyPos "<no source information>"
srcSpanSourcePosE (RealSrcSpan s _) = realSrcSpanSourcePosE s

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
realSrcSpanSourcePos s = safeSourcePos file line col
  where
    file               = unpackFS $ srcSpanFile s
    line               = srcSpanStartLine       s
    col                = srcSpanStartCol        s

realSrcLocSourcePos :: RealSrcLoc -> SourcePos
realSrcLocSourcePos s = safeSourcePos file line col
  where
    file               = unpackFS $ srcLocFile s
    line               = srcLocLine       s
    col                = srcLocCol        s

realSrcSpanSourcePosE :: RealSrcSpan -> SourcePos
realSrcSpanSourcePosE s = safeSourcePos file line col
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

instance F.Loc Var where
  srcSpan v = SS (getSourcePos v) (getSourcePosE v)

namedLocSymbol :: (F.Symbolic a, NamedThing a) => a -> F.Located F.Symbol
namedLocSymbol d = F.symbol <$> locNamedThing d

varLocInfo :: (Type -> a) -> Var -> F.Located a
varLocInfo f x = f . varType <$> locNamedThing x

namedPanic :: (NamedThing a) => a -> String -> b
namedPanic x msg = panic (Just (getSrcSpan x)) msg

--------------------------------------------------------------------------------
-- | Predicates on CoreExpr and DataCons ---------------------------------------
--------------------------------------------------------------------------------

isExternalId :: Id -> Bool
isExternalId = isExternalName . getName

isTupleId :: Id -> Bool
isTupleId = maybe False Ghc.isTupleDataCon . idDataConM

idDataConM :: Id -> Maybe DataCon
idDataConM x = case idDetails x of
  DataConWorkId d -> Just d
  DataConWrapId d -> Just d
  _               -> Nothing

isDataConId :: Id -> Bool
isDataConId = isJust . idDataConM

getDataConVarUnique :: Var -> Unique
getDataConVarUnique v
  | isId v && isDataConId v = getUnique (idDataCon v)
  | otherwise               = getUnique v

isDictionaryExpression :: Ghc.Expr Id -> Maybe Id
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
    go (FunTy { ft_res = res}) = 1 + go res
    go _               = 0


kindArity :: Kind -> Arity
kindArity (ForAllTy _ res)
  = 1 + kindArity res
kindArity _
  = 0

uniqueHash :: Uniquable a => Int -> a -> Int
uniqueHash i = hashWithSalt i . getKey . getUnique

--------------------------------------------------------------------------------
-- | Symbol Conversions --------------------------------------------------------
--------------------------------------------------------------------------------

symbolTyVar :: Symbol -> TyVar
symbolTyVar = stringTyVar . symbolString

localVarSymbol ::  Var -> Symbol
localVarSymbol v
  | us `isSuffixOfSym` vs = vs
  | otherwise             = suffixSymbol vs us
  where
    us                    = symbol $ showPpr $ getDataConVarUnique v
    vs                    = exportedVarSymbol v

exportedVarSymbol :: Var -> Symbol
exportedVarSymbol x = notracepp msg . symbol . getName $ x
  where
    msg = "exportedVarSymbol: " ++ showPpr x

qualifiedNameSymbol :: Name -> Symbol
qualifiedNameSymbol = symbol . Ghc.qualifiedNameFS

instance Symbolic FastString where
  symbol = symbol . fastStringText

fastStringText :: FastString -> T.Text
fastStringText = T.decodeUtf8With TE.lenientDecode . bytesFS

tyConTyVarsDef :: TyCon -> [TyVar]
tyConTyVarsDef c
  | noTyVars c = []
  | otherwise  = Ghc.tyConTyVars c
  --where
  --  none         = tracepp ("tyConTyVarsDef: " ++ show c) (noTyVars c)

noTyVars :: TyCon -> Bool
noTyVars c =  Ghc.isPrimTyCon c || Ghc.isPromotedDataCon c

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
    | isExternalId v = exportedVarSymbol v
    | otherwise      = localVarSymbol    v


instance Hashable Var where
  hashWithSalt = uniqueHash

instance Hashable TyCon where
  hashWithSalt = uniqueHash

instance Hashable Class where
  hashWithSalt = uniqueHash

instance Hashable DataCon where
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

takeModuleUnique :: Symbol -> Symbol
takeModuleUnique = mungeNames tailName sepUnique   "takeModuleUnique: "
  where
    tailName msg = symbol . safeLast msg

splitModuleUnique :: Symbol -> (Symbol, Word64)
splitModuleUnique x = (dropModuleNamesAndUnique x, base62ToW (takeModuleUnique x))

base62ToW :: Symbol -> Word64
base62ToW s =  fromMaybe (errorstar "base62ToW Out Of Range") $ go (F.symbolText s)
  where
    digitToW :: OM.Map Char Word64
    digitToW = OM.fromList $ zip (['0'..'9'] ++ ['a'..'z'] ++ ['A'..'Z']) [0..]
    f acc (flip OM.lookup digitToW -> x) = (acc * 62 +) <$> x
    go = foldM f 0 . T.unpack


splitModuleName :: Symbol -> (Symbol, Symbol)
splitModuleName x = (takeModuleNames x, dropModuleNamesAndUnique x)

dropModuleNamesAndUnique :: Symbol -> Symbol
dropModuleNamesAndUnique = dropModuleUnique . dropModuleNames

dropModuleNames  :: Symbol -> Symbol
dropModuleNames = dropModuleNamesCorrect
{- 
dropModuleNames = mungeNames lastName sepModNames "dropModuleNames: "
 where
   lastName msg = symbol . safeLast msg
-}

dropModuleNamesCorrect  :: Symbol -> Symbol
dropModuleNamesCorrect = F.symbol . go . F.symbolText
  where
    go s = case T.uncons s of
             Just (c,tl) -> if isUpper c  && T.any (== '.') tl
                              then go $ snd $ fromJust $ T.uncons $ T.dropWhile (/= '.') s
                              else s
             Nothing -> s

takeModuleNames  :: Symbol -> Symbol
takeModuleNames  = F.symbol . go [] . F.symbolText
  where
    go acc s = case T.uncons s of
                Just (c,tl) -> if isUpper c && T.any (== '.') tl
                                 then go (getModule' s:acc) $ snd $ fromJust $ T.uncons $ T.dropWhile (/= '.') s
                                 else T.intercalate "." (reverse acc)
                Nothing -> T.intercalate "." (reverse acc)
    getModule' = T.takeWhile (/= '.')

{- 
takeModuleNamesOld  = mungeNames initName sepModNames "takeModuleNames: "
  where
    initName msg = symbol . T.intercalate "." . safeInit msg
-}
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

isQualifiedSym :: Symbol -> Bool
isQualifiedSym (symbolText -> x) = isQualified x

isQualified :: T.Text -> Bool
isQualified y = "." `T.isInfixOf` y

wrapParens :: (IsString a, Monoid a) => a -> a
wrapParens x  = "(" `mappend` x `mappend` ")"

isParened :: T.Text -> Bool
isParened xs  = xs /= stripParens xs

isDictionary :: Symbolic a => a -> Bool
isDictionary = isPrefixOfSym "$f" . dropModuleNames . symbol

isMethod :: Symbolic a => a -> Bool
isMethod = isPrefixOfSym "$c" . dropModuleNames . symbol

isInternal :: Symbolic a => a -> Bool
isInternal   = isPrefixOfSym "$"  . dropModuleNames . symbol

isWorker :: Symbolic a => a -> Bool
isWorker s = notracepp ("isWorkerSym: s = " ++ ss) $ "$W" `L.isInfixOf` ss
  where
    ss     = symbolString (symbol s)

isSCSel :: Symbolic a => a -> Bool
isSCSel  = isPrefixOfSym "$p" . dropModuleNames . symbol

stripParens :: T.Text -> T.Text
stripParens t = fromMaybe t (strip t)
  where
    strip = T.stripPrefix "(" >=> T.stripSuffix ")"

stripParensSym :: Symbol -> Symbol
stripParensSym (symbolText -> t) = symbol (stripParens t)

--------------------------------------------------------------------------------
-- | GHC Compatibility Layer ---------------------------------------------------
--------------------------------------------------------------------------------

gHC_VERSION :: String
gHC_VERSION = show (__GLASGOW_HASKELL__ :: Int)

symbolFastString :: Symbol -> FastString
symbolFastString = mkFastStringByteString . T.encodeUtf8 . symbolText

synTyConRhs_maybe :: TyCon -> Maybe Type
synTyConRhs_maybe = Ghc.synTyConRhs_maybe

showCBs :: Bool -> [CoreBind] -> String
showCBs untidy
  | untidy    =
    Ghc.renderWithContext ctx . ppr . tidyCBs
  | otherwise = showPpr
  where
    ctx = Ghc.defaultSDocContext { sdocPprDebug = True }

ignoreCoreBinds :: S.HashSet Var -> [CoreBind] -> [CoreBind]
ignoreCoreBinds vs cbs
  | S.null vs         = cbs
  | otherwise         = concatMap go cbs
  where
    go :: CoreBind -> [CoreBind]
    go b@(NonRec x _)
      | S.member x vs = []
      | otherwise     = [b]
    go (Rec xes)      = [Rec (filter ((`notElem` vs) . fst) xes)]


findVarDef :: Symbol -> [CoreBind] -> Maybe (Var, CoreExpr)
findVarDef sym cbs = case xCbs of
                     (NonRec v def   : _ ) -> Just (v, def)
                     (Rec [(v, def)] : _ ) -> Just (v, def)
                     _                     -> Nothing
  where
    xCbs            = [ cb | cb <- concatMap unRec cbs, sym `elem` coreBindSymbols cb ]
    unRec (Rec xes) = [NonRec x es | (x,es) <- xes]
    unRec nonRec    = [nonRec]


findVarDefMethod :: Symbol -> [CoreBind] -> Maybe (Var, CoreExpr)
findVarDefMethod sym cbs =
  case rcbs  of
                     (NonRec v def   : _ ) -> Just (v, def)
                     (Rec [(v, def)] : _ ) -> Just (v, def)
                     _                     -> Nothing
  where
    rcbs | isMethod sym = mCbs
         | isDictionary (dropModuleNames sym) = dCbs
         | otherwise  = xCbs
    xCbs            = [ cb | cb <- concatMap unRec cbs, sym `elem` coreBindSymbols cb
                           ]
    mCbs            = [ cb | cb <- concatMap unRec cbs, sym `elem` methodSymbols cb]
    dCbs            = [ cb | cb <- concatMap unRec cbs, sym `elem` dictionarySymbols cb]
    unRec (Rec xes) = [NonRec x es | (x,es) <- xes]
    unRec nonRec    = [nonRec]

dictionarySymbols :: CoreBind -> [Symbol]
dictionarySymbols = filter isDictionary . map (dropModuleNames . symbol) . binders


methodSymbols :: CoreBind -> [Symbol]
methodSymbols = filter isMethod . map (dropModuleNames . symbol) . binders



coreBindSymbols :: CoreBind -> [Symbol]
coreBindSymbols = map (dropModuleNames . simplesymbol) . binders

simplesymbol :: (NamedThing t) => t -> Symbol
simplesymbol = symbol . getName

binders :: Bind a -> [a]
binders (NonRec z _) = [z]
binders (Rec xes)    = fst <$> xes

expandVarType :: Var -> Type
expandVarType = expandTypeSynonyms . varType

--------------------------------------------------------------------------------
-- | The following functions test if a `CoreExpr` or `CoreVar` can be
--   embedded in logic. With type-class support, we can no longer erase
--   such expressions arbitrarily.
--------------------------------------------------------------------------------
isEmbeddedDictExpr :: CoreExpr -> Bool
isEmbeddedDictExpr = isEmbeddedDictType . exprType

isEmbeddedDictVar :: Var -> Bool
isEmbeddedDictVar v = F.notracepp msg . isEmbeddedDictType . varType $ v
  where
    msg     =  "isGoodCaseBind v = " ++ show v

isEmbeddedDictType :: Type -> Bool
isEmbeddedDictType = anyF [isOrdPred, isNumericPred, isEqPred, isPrelEqPred]

-- unlike isNumCls, isFracCls, these two don't check if the argument's
-- superclass is Ord or Num. I believe this is the more predictable behavior

isPrelEqPred :: Type -> Bool
isPrelEqPred ty = case tyConAppTyCon_maybe ty of
  Just tyCon -> isPrelEqTyCon tyCon
  _          -> False


isPrelEqTyCon :: TyCon -> Bool
isPrelEqTyCon tc = tc `hasKey` eqClassKey

isOrdPred :: Type -> Bool
isOrdPred ty = case tyConAppTyCon_maybe ty of
  Just tyCon -> tyCon `hasKey` ordClassKey
  _          -> False

-- Not just Num, but Fractional, Integral as well
isNumericPred :: Type -> Bool
isNumericPred ty = case tyConAppTyCon_maybe ty of
  Just tyCon -> getUnique tyCon `elem` numericClassKeys
  _          -> False



--------------------------------------------------------------------------------
-- | The following functions test if a `CoreExpr` or `CoreVar` are just types
--   in disguise, e.g. have `PredType` (in the GHC sense of the word), and so
--   shouldn't appear in refinements.
--------------------------------------------------------------------------------
isPredExpr :: CoreExpr -> Bool
isPredExpr = isPredType . Ghc.exprType

isPredVar :: Var -> Bool
isPredVar v = F.notracepp msg . isPredType . varType $ v
  where
    msg     =  "isGoodCaseBind v = " ++ show v

isPredType :: Type -> Bool
isPredType = anyF [ isClassPred, isEqPred, isEqPrimPred ]

anyF :: [a -> Bool] -> a -> Bool
anyF ps x = or [ p x | p <- ps ]


-- | 'defaultDataCons t ds' returns the list of '(dc, types)' pairs,
--   corresponding to the _missing_ cases, i.e. _other_ than those in 'ds',
--   that are being handled by DEFAULT.
defaultDataCons :: Type -> [AltCon] -> Maybe [(DataCon, [TyVar], [Type])]
defaultDataCons (TyConApp tc argτs) ds = do
  allDs     <- Ghc.tyConDataCons_maybe tc
  let seenDs = [d | DataAlt d <- ds ]
  let defDs  = keyDiff showPpr allDs seenDs
  return [ (d, Ghc.dataConExTyCoVars d, map irrelevantMult $ Ghc.dataConInstArgTys d argτs) | d <- defDs ]

defaultDataCons _ _ =
  Nothing



isEvVar :: Id -> Bool
isEvVar x = isPredVar x || isTyVar x || isCoVar x


--------------------------------------------------------------------------------
-- | Elaboration
--------------------------------------------------------------------------------

-- FIXME: the handling of exceptions seems to be broken

-- partially stolen from GHC'sa exprType

-- elaborateHsExprInst
--   :: GhcMonad m => LHsExpr GhcPs -> m (Messages, Maybe CoreExpr)
-- elaborateHsExprInst expr = elaborateHsExpr TM_Inst expr


-- elaborateHsExpr
--   :: GhcMonad m => TcRnExprMode -> LHsExpr GhcPs -> m (Messages, Maybe CoreExpr)
-- elaborateHsExpr mode expr =
--   withSession $ \hsc_env -> liftIO $ hscElabHsExpr hsc_env mode expr

-- hscElabHsExpr :: HscEnv -> TcRnExprMode -> LHsExpr GhcPs -> IO (Messages, Maybe CoreExpr)
-- hscElabHsExpr hsc_env0 mode expr = runInteractiveHsc hsc_env0 $ do
--   hsc_env <- Ghc.getHscEnv
--   liftIO $ elabRnExpr hsc_env mode expr

elabRnExpr :: LHsExpr GhcPs -> TcRn CoreExpr
elabRnExpr rdr_expr = do
    (rn_expr, _fvs) <- rnLExpr rdr_expr
    failIfErrsM

    -- Typecheck the expression
    ((tclvl, (tc_expr, res_ty)), lie)
          <- captureTopConstraints $
             pushTcLevelM          $
             tcInferRho rn_expr

    -- Generalise
    uniq <- newUnique
    let { fresh_it = itName uniq (getLocA rdr_expr) }
    ((_qtvs, _dicts, evbs, _), residual)
         <- captureConstraints $
            simplifyInfer tclvl NoRestrictions
                          []    {- No sig vars -}
                          [(fresh_it, res_ty)]
                          lie

    -- Ignore the dictionary bindings
    evbs' <- simplifyInteractive residual
    full_expr <- zonkTopLExpr (mkHsDictLet (EvBinds evbs') (mkHsDictLet evbs tc_expr))
    (ds_msgs, me) <- initDsTc $ dsLExpr full_expr

    logger <- getLogger
    diag_opts <- initDiagOpts <$> getDynFlags
    print_config <- initDsMessageOpts <$> getDynFlags
    liftIO $ printMessages logger print_config diag_opts ds_msgs

    case me of
      Nothing -> failM
      Just e -> do
        when (errorsOrFatalWarningsFound ds_msgs)
          failM
        return e

newtype HashableType = HashableType {getHType :: Type}

instance Eq HashableType where
  x == y = eqType (getHType x) (getHType y)

instance Ord HashableType where
  compare x y = nonDetCmpType (getHType x) (getHType y)

instance Outputable HashableType where
  ppr = ppr . getHType


--------------------------------------------------------------------------------
-- | Superclass coherence
--------------------------------------------------------------------------------

canonSelectorChains :: PredType -> OM.Map HashableType [Id]
canonSelectorChains t = foldr (OM.unionWith const) mempty (zs : xs)
 where
  (cls, ts) = Ghc.getClassPredTys t
  scIdTys   = classSCSelIds cls
  ys        = fmap (\d -> (d, piResultTys (idType d) (ts ++ [t]))) scIdTys
  zs        = OM.fromList $ fmap (\(x, y) -> (HashableType y, [x])) ys
  xs        = fmap (\(d, t') -> fmap (d :) (canonSelectorChains t')) ys

buildCoherenceOblig :: Class -> [[([Id], [Id])]]
buildCoherenceOblig cls = evalState (mapM f xs) OM.empty
 where
  (ts, _, selIds, _) = classBigSig cls
  tts                = mkTyVarTy <$> ts
  t                  = mkClassPred cls tts
  ys = fmap (\d -> (d, piResultTys (idType d) (tts ++ [t]))) selIds
  xs                 = fmap (\(d, t') -> fmap (d:) (canonSelectorChains t')) ys
  f tid = do
    ctid' <- get
    modify (flip (OM.unionWith const) tid)
    pure . OM.elems $ OM.intersectionWith (,) ctid' (fmap tail tid)


-- to be zipped onto the super class selectors
coherenceObligToRef :: (F.Symbolic s) => s -> [Id] -> [Id] -> F.Reft
coherenceObligToRef d = coherenceObligToRefE (F.eVar $ F.symbol d)

coherenceObligToRefE :: F.Expr -> [Id] -> [Id] -> F.Reft
coherenceObligToRefE e rps0 rps1 = F.Reft (F.vv_, F.PAtom F.Eq lhs rhs)
  where lhs = L.foldr EApp e ps0
        rhs = L.foldr EApp (F.eVar F.vv_) ps1
        ps0 = F.eVar . F.symbol <$> L.reverse rps0
        ps1 = F.eVar . F.symbol <$> L.reverse rps1

data TcWiredIn = TcWiredIn {
    tcWiredInName :: Name
  , tcWiredInFixity :: Maybe (Int, FixityDirection)
  , tcWiredInType :: LHsType GhcRn
  }

-- | Run a computation in GHC's typechecking monad with wired in values locally bound in the typechecking environment.
withWiredIn :: TcM a -> TcM a
withWiredIn m = discardConstraints $ do
  -- undef <- lookupUndef
  wiredIns <- mkWiredIns
  -- snd <$> tcValBinds Ghc.NotTopLevel (binds undef wiredIns) (sigs wiredIns) m
  (_, _, a) <- tcValBinds Ghc.NotTopLevel [] (sigs wiredIns) m
  return a

 where
  -- lookupUndef = do
  --   lookupOrig gHC_ERR (Ghc.mkVarOcc "undefined")
  --   -- tcLookupGlobal undefName

  -- binds :: Name -> [TcWiredIn] -> [(Ghc.RecFlag, LHsBinds GhcRn)]
  -- binds undef wiredIns = map (\w -> 
  --     let ext = Ghc.unitNameSet undef in -- $ varName $ tyThingId undef in
  --     let co_fn = idHsWrapper in
  --     let matches = 
  --           let ctxt = LambdaExpr in
  --           let grhss = GRHSs Ghc.noExtField [Ghc.L locSpan (GRHS Ghc.noExtField [] (Ghc.L locSpan (HsVar Ghc.noExtField (Ghc.L locSpan undef))))] (Ghc.L locSpan emptyLocalBinds) in
  --           MG Ghc.noExtField (Ghc.L locSpan [Ghc.L locSpan (Match Ghc.noExtField ctxt [] grhss)]) Ghc.Generated 
  --     in
  --     let b = FunBind ext (Ghc.L locSpan $ tcWiredInName w) matches co_fn [] in
  --     (Ghc.NonRecursive, unitBag (Ghc.L locSpan b))
  --   ) wiredIns

  sigs wiredIns = concatMap (\w ->
      let inf = maybeToList $ (\(fPrec, fDir) -> Ghc.L locSpanAnn $ Ghc.FixSig Ghc.noAnn $ Ghc.FixitySig Ghc.NoNamespaceSpecifier [Ghc.L locSpanAnn (tcWiredInName w)] $ Ghc.Fixity Ghc.NoSourceText fPrec fDir) <$> tcWiredInFixity w in
      let t =
            let ext' = [] in
            [Ghc.L locSpanAnn $ TypeSig Ghc.noAnn [Ghc.L locSpanAnn (tcWiredInName w)] $ HsWC ext' $ Ghc.L locSpanAnn $ HsSig Ghc.noExtField (HsOuterImplicit ext') $ tcWiredInType w]
      in
      inf <> t
    ) wiredIns

  locSpan = UnhelpfulSpan (UnhelpfulOther "Liquid.GHC.Misc: WiredIn")
  locSpanAnn = noAnnSrcSpan locSpan

  mkHsFunTy :: LHsType GhcRn -> LHsType GhcRn -> LHsType GhcRn
  mkHsFunTy a b = nlHsFunTy a b

  mkWiredIns = sequence [impl, dimpl, eq, len]

  toName s = do
    u <- getUniqueM
    return $ Ghc.mkInternalName u (Ghc.mkVarOcc s) locSpan

  toLoc = Ghc.L locSpanAnn
  nameToTy = Ghc.L locSpanAnn . HsTyVar Ghc.noAnn Ghc.NotPromoted

  boolTy' :: LHsType GhcRn
  boolTy' = nameToTy $ toLoc boolTyConName
    -- boolName <- lookupOrig (Module (stringToUnitId "Data.Bool") (mkModuleName "Data.Bool")) (Ghc.mkVarOcc "Bool")
    -- return $ Ghc.L locSpan $ HsTyVar Ghc.noExtField Ghc.NotPromoted $ Ghc.L locSpan boolName
  intTy' = nameToTy $ toLoc intTyConName
  listTy lt = toLoc $ HsAppTy Ghc.noExtField (nameToTy $ toLoc listTyConName) lt

  -- infixr 1 ==> :: Bool -> Bool -> Bool
  impl = do
    n <- toName "==>"
    let ty = mkHsFunTy boolTy' (mkHsFunTy boolTy' boolTy')
    return $ TcWiredIn n (Just (1, Ghc.InfixR)) ty

  -- infixr 1 <=> :: Bool -> Bool -> Bool
  dimpl = do
    n <- toName "<=>"
    let ty = mkHsFunTy boolTy' (mkHsFunTy boolTy' boolTy')
    return $ TcWiredIn n (Just (1, Ghc.InfixR)) ty

  -- infix 4 == :: forall a . a -> a -> Bool
  eq = do
    n <- toName "=="
    aName <- toLoc <$> toName "a"
    let aTy = nameToTy aName
    let ty = toLoc $ HsForAllTy Ghc.noExtField
             (mkHsForAllInvisTele Ghc.noAnn [toLoc $ UserTyVar Ghc.noAnn SpecifiedSpec aName]) $ mkHsFunTy aTy (mkHsFunTy aTy boolTy')
    return $ TcWiredIn n (Just (4, Ghc.InfixN)) ty

  -- TODO: This is defined as a measure in liquidhaskell GHC.Base_LHAssumptions. We probably want to insert all measures to the environment.
  -- len :: forall a. [a] -> Int
  len = do
    n <- toName "len"
    aName <- toLoc <$> toName "a"
    let aTy = nameToTy aName
    let ty = toLoc $ HsForAllTy Ghc.noExtField
               (mkHsForAllInvisTele Ghc.noAnn [toLoc $ UserTyVar Ghc.noAnn SpecifiedSpec aName]) $ mkHsFunTy (listTy aTy) intTy'
    return $ TcWiredIn n Nothing ty

prependGHCRealQual :: FastString -> RdrName
prependGHCRealQual = varQual_RDR gHC_INTERNAL_REAL

isFromGHCReal :: NamedThing a => a -> Bool
isFromGHCReal x = Ghc.nameModule (Ghc.getName x) == gHC_INTERNAL_REAL
