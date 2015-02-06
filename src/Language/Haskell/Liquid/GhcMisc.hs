{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE UndecidableInstances      #-}

-- | This module contains a wrappers and utility functions for
-- accessing GHC module information. It should NEVER depend on
-- ANY module inside the Language.Haskell.Liquid.* tree.

module Language.Haskell.Liquid.GhcMisc where

import PrelNames (fractionalClassKeys)
import Class     (classKey)

import           Debug.Trace

import           Avail                        (availsToNameSet)
import           CoreSyn                      hiding (Expr)
import qualified CoreSyn as Core
import           CostCentre
import           GHC                          hiding (L)
import           HscTypes                     (Dependencies, ImportedMods, ModGuts(..))
import           Kind                         (superKind)
import           NameSet                      (NameSet)
import           SrcLoc                       (mkRealSrcLoc, mkRealSrcSpan, srcSpanFileName_maybe)

import           Language.Fixpoint.Names      (dropModuleNames)
import           Text.Parsec.Pos              (sourceName, sourceLine, sourceColumn, SourcePos, newPos)
import           Language.Fixpoint.Types      hiding (Constant (..), SESearch(..))
import           Name                         (mkInternalName, getSrcSpan, nameModule_maybe)
import           Module                       (moduleNameFS)
import           OccName                      (mkTyVarOcc, mkTcOcc, occNameFS)
import           Unique
import           Finder                       (findImportedModule, cannotFindModule)
import           Panic                        (throwGhcException)
import           HscTypes                     (HscEnv(..), FindResult(..))
import           FastString
import           TcRnDriver

import           RdrName
import           Type                         (liftedTypeKind)
import           TypeRep
import           Var
import qualified TyCon                        as TC
import           Data.Char                    (isLower, isSpace)
import           Data.Monoid                  (mempty)
import           Data.Hashable
import qualified Data.HashSet                 as S
import qualified Data.List                    as L
import           Data.Aeson                 
import qualified Data.Text.Encoding           as T
import qualified Data.Text.Unsafe             as T
import           Control.Applicative          ((<$>), (<*>))
import           Control.Arrow                (second)
import           Outputable                   (Outputable (..), text, ppr)
import qualified Outputable                   as Out
import           DynFlags

import qualified Text.PrettyPrint.HughesPJ    as PJ

import Data.Monoid (mappend)

import Language.Fixpoint.Names      (symSepName, isSuffixOfSym, singletonSym)

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
  , mgi_is_dfun   :: !(Maybe [DFunId])
  }

miModGuts dids mg = MI {
    mgi_binds     = mg_binds mg
  , mgi_module    = mg_module mg
  , mgi_deps      = mg_deps mg
  , mgi_dir_imps  = mg_dir_imps mg
  , mgi_rdr_env   = mg_rdr_env mg
  , mgi_tcs       = mg_tcs mg
  , mgi_fam_insts = mg_fam_insts mg
  , mgi_exports   = availsToNameSet $ mg_exports mg
  , mgi_is_dfun   = dids
  }

-----------------------------------------------------------------------
--------------- Generic Helpers for Encoding Location -----------------
-----------------------------------------------------------------------

srcSpanTick :: Module -> SrcSpan -> Tickish a
srcSpanTick m loc
  = ProfNote (AllCafsCC m loc) False True

tickSrcSpan ::  Outputable a => Tickish a -> SrcSpan
tickSrcSpan (ProfNote cc _ _) = cc_loc cc
tickSrcSpan _                 = noSrcSpan 
-----------------------------------------------------------------------
--------------- Generic Helpers for Accessing GHC Innards -------------
-----------------------------------------------------------------------

stringTyVar :: String -> TyVar
stringTyVar s = mkTyVar name liftedTypeKind
  where name = mkInternalName (mkUnique 'x' 24)  occ noSrcSpan
        occ  = mkTyVarOcc s

stringTyCon :: Char -> Int -> String -> TyCon
stringTyCon c n s = TC.mkKindTyCon name superKind
  where 
    name          = mkInternalName (mkUnique c n) occ noSrcSpan
    occ           = mkTcOcc s

hasBaseTypeVar = isBaseType . varType

-- same as Constraint isBase
isBaseType (TyVarTy _)     = True
isBaseType (TyConApp _ ts) = all isBaseType ts
isBaseType (FunTy t1 t2)   = isBaseType t1 && isBaseType t2
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

getDataConVarUnique v
  | isId v && isDataConWorkId v = getUnique $ idDataCon v
  | otherwise                   = getUnique v
  

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
showPpr      = Out.showPpr unsafeGlobalDynFlags
showSDoc     = Out.showSDoc unsafeGlobalDynFlags
showSDocDump = Out.showSDocDump unsafeGlobalDynFlags

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

getSourcePos           = srcSpanSourcePos . getSrcSpan 


collectArguments n e = if length xs > n then take n xs else xs
  where (vs', e') = collectValBinders' $ snd $ collectTyBinders e
        vs        = fst $ collectValBinders $ ignoreLetBinds e'
        xs        = vs' ++ vs

collectValBinders' expr = go [] expr
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

isDictionary x = L.isPrefixOf "$f" (symbolString $ dropModuleNames $ symbol x)
isInternal   x = L.isPrefixOf "$"  (symbolString $ dropModuleNames $ symbol x)


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
  | otherwise             = vs `mappend` singletonSym symSepName `mappend` us
  where us  = symbol $ showPpr $ getDataConVarUnique v
        vs  = symbol $ getName v


qualifiedNameSymbol n = symbol $
  case nameModule_maybe n of
    Nothing -> occNameFS (getOccName n)
    Just m  -> concatFS [moduleNameFS (moduleName m), fsLit ".", occNameFS (getOccName n)]

instance Symbolic FastString where
  symbol = symbol . fastStringText

fastStringText = T.decodeUtf8 . fastStringToByteString
symbolFastString = T.unsafeDupablePerformIO . mkFastStringByteString . T.encodeUtf8 . symbolText
