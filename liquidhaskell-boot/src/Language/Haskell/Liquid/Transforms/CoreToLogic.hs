{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE MagicHash              #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE TemplateHaskellQuotes  #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE UndecidableInstances   #-}

{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-x-partial #-}

module Language.Haskell.Liquid.Transforms.CoreToLogic
  ( coreToDef
  , coreToFun
  , coreToLogic
  , mkLit, mkI, mkS
  , runToLogic
  , runToLogicWithBoolBinds
  , logicType
  , inlineSpecType
  , measureSpecType
  , weakenResult
  , normalize
  ) where

import           Data.Bifunctor (first)
import           Data.ByteString                       (ByteString)
import           Prelude                               hiding (error)
import           Language.Haskell.Liquid.GHC.TypeRep   () -- needed for Eq 'Type'
import           Liquid.GHC.API       hiding (Expr, Located, get, panic)
import qualified Liquid.GHC.API       as Ghc
import qualified Liquid.GHC.API       as C
import qualified Data.List                             as L
import           Data.Maybe                            (listToMaybe)
import qualified Data.Text                             as T
import qualified Data.Char
import qualified Text.Printf as Printf
import           Data.Text.Encoding
import           Data.Text.Encoding.Error
import           Control.Monad.Except
import           Control.Monad.Identity
import qualified Language.Haskell.Liquid.Misc          as Misc
import           Language.Fixpoint.Types               hiding (panic, Error, R, simplify, isBool)
import qualified Language.Fixpoint.Types               as F
import qualified Language.Haskell.Liquid.GHC.Misc      as GM


import           Language.Haskell.Liquid.Bare.Types
import           Language.Haskell.Liquid.Bare.DataType
import           Language.Haskell.Liquid.Bare.Misc     (simpleSymbolVar)
import           Language.Haskell.Liquid.GHC.Play
import           Language.Haskell.Liquid.Types.Errors
import           Language.Haskell.Liquid.Types.Names
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Types.RType
import           Language.Haskell.Liquid.Types.RTypeOp
import           Language.Haskell.Liquid.Types.Types

import qualified Data.HashMap.Strict                   as M
import Control.Monad.Reader
import Language.Haskell.Liquid.UX.Config

import Data.Ratio
import GHC.Base ((+#), (-#), (*#))
import GHC.Num

logicType :: (Reftable r) => Bool -> Type -> RRType r
logicType allowTC τ      = fromRTypeRep $ t { ty_binds = bs, ty_info = is, ty_args = as, ty_refts = rs}
  where
    t            = toRTypeRep $ ofType τ
    (bs, is, as, rs) = Misc.unzip4 $ dropWhile (isErasable' . Misc.thd4) $ Misc.zip4 (ty_binds t) (ty_info t) (ty_args t) (ty_refts t)
    isErasable'  = if allowTC then isEmbeddedClass else isClassType

{- | [NOTE:inlineSpecType type]: the refinement depends on whether the result type is a Bool or not:
      CASE1: measure f@logic :: X -> Bool <=> f@haskell :: x:X -> {v:Bool | v <=> (f@logic x)}
     CASE2: measure f@logic :: X -> Y    <=> f@haskell :: x:X -> {v:Y    | v = (f@logic x)}
 -}
-- formerly: strengthenResult
inlineSpecType :: Bool -> Var -> SpecType
inlineSpecType  allowTC v = fromRTypeRep $ rep {ty_res = res `strengthen` r , ty_binds = xs}
  where
    r              = MkUReft (mkReft (mkEApp f (mkA <$> vxs))) mempty
    rep            = toRTypeRep t
    res            = ty_res rep
    xs             = intSymbol (symbol ("x" :: String)) <$> [1..length $ ty_binds rep]
    vxs            = dropWhile (isErasable' . snd) $ zip xs (ty_args rep)
    isErasable'    = if allowTC then isEmbeddedClass else isClassType
    f              = dummyLoc (symbol v)
    t              = ofType (GM.expandVarType v) :: SpecType
    mkA            = EVar . fst
    mkReft         = if isBool res then propReft else exprReft

-- | Refine types of measures: keep going until you find the last data con!
--   this code is a hack! we refine the last data constructor,
--   it got complicated to support both
--   1. multi parameter measures     (see tests/pos/HasElem.hs)
--   2. measures returning functions (fromReader :: Reader r a -> (r -> a) )
--   TODO: SIMPLIFY by dropping support for multi parameter measures

-- formerly: strengthenResult'
measureSpecType :: Bool -> Var -> SpecType
measureSpecType allowTC v = go mkT [] [(1::Int)..] st
  where
    mkReft | boolRes   = propReft
           | otherwise = exprReft
    mkT xs          = MkUReft (mkReft $ mkEApp locSym (EVar <$> reverse xs)) mempty
    locSym          = dummyLoc (symbol v)
    st              = ofType (GM.expandVarType v) :: SpecType
    boolRes         =  isBool $ ty_res $ toRTypeRep st

    go f args i (RAllT a t r)    = RAllT a (go f args i t) r
    go f args i (RAllP p t)      = RAllP p $ go f args i t
    go f args i (RFun x ii t1 t2 r)
     | (if allowTC then isEmbeddedClass else isClassType) t1           = RFun x ii t1 (go f args i t2) r
    go f args i t@(RFun _ ii t1 t2 r)
     | hasRApps t               = RFun x' ii t1 (go f (x':args) (tail i) t2) r
                                       where x' = intSymbol (symbol ("x" :: String)) (head i)
    go f args _ t                = t `strengthen` f args

    hasRApps (RFun _ _ t1 t2 _) = hasRApps t1 || hasRApps t2
    hasRApps RApp {}          = True
    hasRApps _                = False


-- | 'weakenResult foo t' drops the singleton constraint `v = foo x y`
--   that is added, e.g. for measures in /strengthenResult'.
--   This should only be used _when_ checking the body of 'foo'
--   where the output, is, by definition, equal to the singleton.
weakenResult :: Bool -> Var -> SpecType -> SpecType
weakenResult allowTC v t = F.notracepp msg t'
  where
    msg          = "weakenResult v =" ++ GM.showPpr v ++ " t = " ++ showpp t
    t'           = fromRTypeRep $ rep { ty_res = mapExprReft weaken (ty_res rep) }
    rep          = toRTypeRep t
    weaken x     = pAnd . filter ((Just vE /=) . isSingletonExpr x) . conjuncts
    vE           = mkEApp vF xs
    xs           = EVar . fst <$> dropWhile ((if allowTC then isEmbeddedClass else isClassType) . snd) xts
    xts          = zip (ty_binds rep) (ty_args rep)
    vF           = dummyLoc (symbol v)

type LogicM = ExceptT Error (ReaderT LState Identity)

data LState = LState
  { lsSymMap  :: LogicMap
  , lsError   :: String -> Error
  , lsEmb     :: TCEmb TyCon
  , lsBools   :: [Var]
  , lsDCMap   :: DataConMap
  , lsConfig  :: Config
  }

throw :: String -> LogicM a
throw str = do
  fmkError  <- reader lsError
  throwError $ fmkError str

getState :: LogicM LState
getState = ask

runToLogic
  :: TCEmb TyCon -> LogicMap -> DataConMap -> Config -> (String -> Error)
  -> LogicM t -> Either Error t
runToLogic = runToLogicWithBoolBinds []

runToLogicWithBoolBinds
  :: [Var] -> TCEmb TyCon -> LogicMap -> DataConMap -> Config -> (String -> Error)
  -> LogicM t -> Either Error t
runToLogicWithBoolBinds xs tce lmap dm cfg ferror m
  = runReader (runExceptT m) $ LState
      { lsSymMap = lmap
      , lsError  = ferror
      , lsEmb    = tce
      , lsBools  = xs
      , lsDCMap  = dm
      , lsConfig = cfg
      }

coreAltToDef :: (Reftable r) => Located LHName -> Var -> [Var] -> Var -> Type -> [C.CoreAlt]
             -> LogicM [Def (Located (RRType r)) DataCon]
coreAltToDef locSym z zs y t alts
  | not (null litAlts) = measureFail locSym "Cannot lift definition with literal alternatives"
  | otherwise          = do
      d1s <- F.notracepp "coreAltDefs-1" <$> mapM (mkAlt locSym cc myArgs z) dataAlts
      d2s <- F.notracepp "coreAltDefs-2" <$>       mkDef locSym cc myArgs z  defAlts defExpr
      return (d1s ++ d2s)
  where
    myArgs   = reverse zs
    cc       = if eqType t boolTy then P else E
    defAlts  = GM.defaultDataCons (GM.expandVarType y) ((\(Alt c _ _) -> c) <$> alts)
    defExpr  = listToMaybe [ e |   (Alt C.DEFAULT _ e) <- alts ]
    dataAlts =             [ a | a@(Alt (C.DataAlt _) _ _) <- alts ]
    litAlts  =             [ a | a@(Alt (C.LitAlt _) _ _) <- alts ]

    -- mkAlt :: LocSymbol -> (Expr -> Body) -> [Var] -> Var -> (C.AltCon, [Var], C.CoreExpr)
    mkAlt x ctor _args dx (Alt (C.DataAlt d) xs e)
      = do
          allowTC <- reader (typeclass . lsConfig)
          let xs' = filter (not . if allowTC then GM.isEmbeddedDictVar else GM.isEvVar) xs
          Def x {- (toArgs id args) -} d (Just $ varRType dx) (toArgs Just xs')
               . ctor
               . (`subst1` (F.symbol dx, F.mkEApp (GM.namedLocSymbol d) (F.eVar <$> xs')))
              <$> coreToLg e
    mkAlt _ _ _ _ alt
      = throw $ "Bad alternative" ++ GM.showPpr alt

    mkDef x ctor _args dx (Just dtss) (Just e) = do
      eDef   <- ctor <$> coreToLg e
      -- let ys  = toArgs id args
      let dxt = Just (varRType dx)
      return  [ Def x {- ys -} d dxt (defArgs x ts) eDef | (d, _, ts) <- dtss ]

    mkDef _ _ _ _ _ _ =
      return []

toArgs :: Reftable r => (Located (RRType r) -> b) -> [Var] -> [(Symbol, b)]
toArgs f args = [(symbol x, f $ varRType x) | x <- args]

defArgs :: Monoid r => Located LHName -> [Type] -> [(Symbol, Maybe (Located (RRType r)))]
defArgs x     = zipWith (\i t -> (defArg i, defRTyp t)) [0..]
  where
    defArg    = tempSymbol (lhNameToResolvedSymbol $ val x)
    defRTyp   = Just . F.atLoc x . ofType

coreToDef :: Reftable r => Located LHName -> Var -> C.CoreExpr
          -> LogicM [Def (Located (RRType r)) DataCon]
coreToDef locSym _ s              = do 
    allowTC <- reader $ typeclass . lsConfig
    go [] $ inlinePreds $ simplify allowTC s
  where
    go args   (C.Lam  x e)        = go (x:args) e
    go args   (C.Tick _ e)        = go args e
    go (z:zs) (C.Case _ y t alts) = coreAltToDef locSym z zs y t alts
    go (z:zs) e
      | Just t <- isMeasureArg z  = coreAltToDef locSym z zs z t [Alt C.DEFAULT [] e]
    go _ _                        = measureFail locSym "Does not have a case-of at the top-level"

    inlinePreds   = inline (eqType boolTy . GM.expandVarType)

measureFail       :: Located LHName -> String -> a
measureFail x msg = panic sp e
  where
    sp            = Just (GM.fSrcSpan x)
    e             = Printf.printf "Cannot create measure '%s': %s" (F.showpp x) msg


-- | 'isMeasureArg x' returns 'Just t' if 'x' is a valid argument for a measure.
isMeasureArg :: Var -> Maybe Type
isMeasureArg x
  | Just tc <- tcMb
  , Ghc.isAlgTyCon tc = F.notracepp "isMeasureArg" $ Just t
  | otherwise           = Nothing
  where
    t                   = GM.expandVarType x
    tcMb                = tyConAppTyCon_maybe t


varRType :: (Reftable r) => Var -> Located (RRType r)
varRType = GM.varLocInfo ofType

coreToFun :: LocSymbol -> Var -> C.CoreExpr ->  LogicM ([Var], Either Expr Expr)
coreToFun _ _v s = do 
  allowTC <- reader $ typeclass . lsConfig
  go [] $ normalize allowTC s
  where
    go acc (C.Lam x e)  | isTyVar x = go acc e
    go acc (C.Lam x e)  = do 
      allowTC <- reader $ typeclass . lsConfig
      let isE = if allowTC then GM.isEmbeddedDictVar else isErasable
      if isE x then go acc e else go (x:acc) e
    go acc (C.Tick _ e) = go acc e
    go acc e            = (reverse acc,) . Right <$> coreToLg e


instance Show C.CoreExpr where
  show = GM.showPpr

coreToLogic :: C.CoreExpr -> LogicM Expr
coreToLogic cb = do
  allowTC <- reader $ typeclass . lsConfig
  coreToLg $ normalize allowTC cb


coreToLg :: C.CoreExpr -> LogicM Expr
coreToLg (C.Let (C.NonRec x (C.Coercion c)) e)
  = coreToLg (C.substExpr (C.extendCvSubst C.emptySubst x c) e)
coreToLg (C.Let b e)
  = subst1 <$> coreToLg e <*> makesub b
coreToLg (C.Tick _ e)          = coreToLg e
coreToLg (C.App (C.Var v) e)
  | ignoreVar v                = coreToLg e
coreToLg (C.Var x)
  | x == falseDataConId        = return PFalse
  | x == trueDataConId         = return PTrue
  | otherwise                  = eVarWithMap x . lsSymMap <$> getState
coreToLg e@(C.App _ _)         = toPredApp e
coreToLg (C.Case e b _ alts)
  | eqType (GM.expandVarType b) boolTy  = checkBoolAlts alts >>= coreToIte e
-- coreToLg (C.Lam x e)           = do p     <- coreToLg e
--                                     tce   <- lsEmb <$> getState
--                                     return $ ELam (symbol x, typeSort tce (GM.expandVarType x)) p
coreToLg (C.Case e b _ alts)   = do p <- coreToLg e
                                    casesToLg b p alts
coreToLg (C.Lit l)             = case mkLit l of
                                          Nothing -> throw $ "Bad Literal in measure definition" ++ GM.showPpr l
                                          Just i  -> return i
coreToLg (C.Cast e c)          = do (s, t) <- coerceToLg c
                                    e'     <- coreToLg e
                                    return (ECoerc s t e')
-- elaboration reuses coretologic
-- TODO: fix this
coreToLg (C.Lam x e) = do p     <- coreToLg e
                          tce   <- lsEmb <$> getState
                          return $ ELam (symbol x, typeSort tce (GM.expandVarType x)) p
coreToLg e                     = throw ("Cannot transform to Logic:\t" ++ GM.showPpr e)




coerceToLg :: Coercion -> LogicM (Sort, Sort)
coerceToLg = typeEqToLg . coercionTypeEq

coercionTypeEq :: Coercion -> (Type, Type)
coercionTypeEq co
  | Ghc.Pair s t <- -- GM.tracePpr ("coercion-type-eq-1: " ++ GM.showPpr co) $
                       coercionKind co
  = (s, t)

typeEqToLg :: (Type, Type) -> LogicM (Sort, Sort)
typeEqToLg (s, t) = do
  tce   <- reader lsEmb
  let tx = typeSort tce . expandTypeSynonyms
  return $ F.notracepp "TYPE-EQ-TO-LOGIC" (tx s, tx t)

checkBoolAlts :: [C.CoreAlt] -> LogicM (C.CoreExpr, C.CoreExpr)
checkBoolAlts [Alt (C.DataAlt false) [] efalse, Alt (C.DataAlt true) [] etrue]
  | false == falseDataCon, true == trueDataCon
  = return (efalse, etrue)

checkBoolAlts [Alt (C.DataAlt true) [] etrue, Alt (C.DataAlt false) [] efalse]
  | false == falseDataCon, true == trueDataCon
  = return (efalse, etrue)
checkBoolAlts alts
  = throw ("checkBoolAlts failed on " ++ GM.showPpr alts)

casesToLg :: Var -> Expr -> [C.CoreAlt] -> LogicM Expr
casesToLg v e alts = mapM (altToLg e) normAlts >>= go
  where
    normAlts       = normalizeAlts alts
    go :: [(C.AltCon, Expr)] -> LogicM Expr
    go [(_,p)]     = return (p `subst1` su)
    go ((d,p):dps) = do c <- checkDataAlt d e
                        e' <- go dps
                        return (EIte c p e' `subst1` su)
    go []          = panic (Just (getSrcSpan v)) $ "Unexpected empty cases in casesToLg: " ++ show e
    su             = (symbol v, e)

checkDataAlt :: C.AltCon -> Expr -> LogicM Expr
checkDataAlt (C.DataAlt d) e = return $ EApp (EVar (makeDataConChecker d)) e
checkDataAlt C.DEFAULT     _ = return PTrue
checkDataAlt (C.LitAlt l)  e
  | Just le <- mkLit l       = return (EEq le e)
  | otherwise                = throw $ "Oops, not yet handled: checkDataAlt on Lit: " ++ GM.showPpr l

-- | 'altsDefault' reorders the CoreAlt to ensure that 'DEFAULT' is at the end.
normalizeAlts :: [C.CoreAlt] -> [C.CoreAlt]
normalizeAlts alts      = ctorAlts ++ defAlts
  where
    (defAlts, ctorAlts) = L.partition isDefault alts
    isDefault (Alt c _ _)   = c == C.DEFAULT

altToLg :: Expr -> C.CoreAlt -> LogicM (C.AltCon, Expr)
altToLg de (Alt a@(C.DataAlt d) xs e) = do
  ctorReflected <- reader (exactDCFlag . lsConfig)
  if not ctorReflected && not (primDataCon d) then do
    throw $  "Cannot lift to logic the constructor `" ++ show d
          ++ "` consider enabling either --exactdc or --reflection"
  else do
    p  <- coreToLg e
    dm <- reader lsDCMap
    allowTC <- reader (typeclass . lsConfig)
    let su = mkSubst $ concat [ dataConProj dm de d x i | (x, i) <- zip (filter (not . if allowTC then GM.isEmbeddedDictVar else GM.isEvVar) xs) [1..]]
    return (a, subst su p)

altToLg _ (Alt a _ e)
  = (a, ) <$> coreToLg e

dataConProj :: DataConMap -> Expr -> DataCon -> Var -> Int -> [(Symbol, Expr)]
dataConProj dm de d x i = [(symbol x, t), (GM.simplesymbol x, t)]
  where
    t | primDataCon  d  = de
      | otherwise       = EApp (EVar $ makeDataConSelector (Just dm) d i) de

primDataCon :: DataCon -> Bool
primDataCon d = d == intDataCon

coreToIte :: C.CoreExpr -> (C.CoreExpr, C.CoreExpr) -> LogicM Expr
coreToIte e (efalse, etrue)
  = do p  <- coreToLg e
       e1 <- coreToLg efalse
       e2 <- coreToLg etrue
       return $ EIte p e2 e1

toPredApp :: C.CoreExpr -> LogicM Expr
toPredApp p = do
  allowTC <- reader (typeclass . lsConfig)
  go . first opSym . splitArgs allowTC $ p
  where
    opSym = tomaybesymbol
    go (Just f, [e1, e2])
      | Just rel <- M.lookup f brels
      = PAtom rel <$> coreToLg e1 <*> coreToLg e2
    go (Just f, [e])
      | f == symbol (show 'not)
      = PNot <$>  coreToLg e
    go (Just f, [e1, e2])
      | f == symbol (show '(||))
      = POr <$> mapM coreToLg [e1, e2]
      | f == symbol (show '(&&))
      = PAnd <$> mapM coreToLg [e1, e2]
      | f == symbol ("Language.Haskell.Liquid.Prelude.==>" :: String)
      = PImp <$> coreToLg e1 <*> coreToLg e2
      | f == symbol ("Language.Haskell.Liquid.Prelude.<=>" :: String)
      = PIff <$> coreToLg e1 <*> coreToLg e2
      | f == symbol (show 'const)
      = coreToLg e1
    go (Just f, [es])
      | f == symbol (show 'or)
      = POr  . deList <$> coreToLg es
      | f == symbol (show 'and)
      = PAnd . deList <$> coreToLg es
    go (_, _)
      = toLogicApp p

    deList :: Expr -> [Expr]
    deList (EApp (EApp (EVar cons) e) es)
      | cons == symbol (show '(:))
      = e:deList es
    deList (EVar nil)
      | nil == symbol (show '[])
      = []
    deList e
      = [e]

toLogicApp :: C.CoreExpr -> LogicM Expr
toLogicApp e = do
  allowTC <- reader (typeclass . lsConfig)
  let (f, es) = splitArgs allowTC e
  case f of
    C.Var _ -> do args <- mapM coreToLg es
                  lmap <- lsSymMap <$> getState
                  def  <- (`mkEApp` args) <$> tosymbol f
                  (\x -> makeApp def lmap x args) <$> tosymbol' f
    _       -> do fe   <- coreToLg f
                  args <- mapM coreToLg es
                  return $ foldl EApp fe args

makeApp :: Expr -> LogicMap -> Located Symbol-> [Expr] -> Expr
makeApp _ _ f [e]
  | val f == symbol (show 'negate)
  = ENeg e
  | val f == symbol (show 'fromInteger)
  , ECon c <- e
  = ECon c
  | (modName, sym) <- GM.splitModuleName (val f)
  , symbol ("Ghci" :: String) `isPrefixOfSym` modName
  , sym == "len"
  = EApp (EVar sym) e

makeApp _ _ f [e1, e2]
  | Just op <- M.lookup (val f) bops
  = EBin op e1 e2
  -- Hack for typeclass support. (overriden == without Eq constraint defined at Ghci)
  | (modName, sym) <- GM.splitModuleName (val f)
  , symbol ("Ghci" :: String) `isPrefixOfSym` modName
  , Just op <- M.lookup (mappendSym (symbol ("GHC.Internal.Num." :: String)) sym) bops
  = EBin op e1 e2

makeApp def lmap f es =
    eAppWithMap lmap (val f) es def
  -- where msg = "makeApp f = " ++ show f ++ " es = " ++ show es ++ " def = " ++ show def

eVarWithMap :: Id -> LogicMap -> Expr
eVarWithMap x lmap = do
    eAppWithMap lmap (symbol x) [] (EVar $ symbol x)

brels :: M.HashMap Symbol Brel
brels = M.fromList [ (symbol (show '(==)), Eq)
                   , (symbol (show '(/=)), Ne)
                   , (symbol (show '(>=)), Ge)
                   , (symbol (show '(>)) , Gt)
                   , (symbol (show '(<=)), Le)
                   , (symbol (show '(<)) , Lt)
                   ]

-- bops is a map between GHC function names/symbols and binary operators
-- from the logic. We want GHC functions like +, -, etc. to map to the
-- corresponding operators. There are actually multiple sources for +, -,
-- they can come from GHC.Prim, GHC.Internal.Num, GHC.Internal.Real or
-- be an instance of Num for Int.
bops :: M.HashMap Symbol Bop
bops = M.fromList [ (symbol (show '(+)), Plus)
                  , (numIntSymbol "+", Plus)
                  , (symbol (show '(+#)), Plus)
                  , (symbol (show '(-)), Minus)
                  , (numIntSymbol "-", Minus)
                  , (symbol (show '(-#)), Minus)
                  , (symbol (show '(*)), Times)
                  , (numIntSymbol "*", Times)
                  , (symbol (show '(*#)), Times)
                  , (symbol (show '(/)), Div)
                  , (symbol (show '(%)), Mod)
                  ]
  where
    numIntSymbol :: String -> Symbol
    numIntSymbol = symbol . (++) "GHC.Internal.Num.$fNumInt_$c"

splitArgs :: Bool -> C.Expr t -> (C.Expr t, [C.Arg t])
splitArgs allowTC exprt = (exprt', reverse args)
 where
    (exprt', args) = go exprt

    go (C.App (C.Var i) e) | ignoreVar i       = go e
    go (C.App f (C.Var v)) | if allowTC then GM.isEmbeddedDictVar v else isErasable v   = go f
    go (C.App f e) = (f', e:es) where (f', es) = go f
    go f           = (f, [])

tomaybesymbol :: C.CoreExpr -> Maybe Symbol
tomaybesymbol (C.Var x) = Just $ symbol x
tomaybesymbol _         = Nothing

tosymbol :: C.CoreExpr -> LogicM (Located Symbol)
tosymbol e
 = case tomaybesymbol e of
    Just x -> return $ dummyLoc x
    _      -> throw ("Bad Measure Definition:\n" ++ GM.showPpr e ++ "\t cannot be applied")

tosymbol' :: C.CoreExpr -> LogicM (Located Symbol)
tosymbol' (C.Var x) = return $ dummyLoc $ symbol x
tosymbol' e        = throw ("Bad Measure Definition:\n" ++ GM.showPpr e ++ "\t cannot be applied")

makesub :: C.CoreBind -> LogicM (Symbol, Expr)
makesub (C.NonRec x e) = (symbol x,) <$> coreToLg e
makesub _              = throw "Cannot make Logical Substitution of Recursive Definitions"

mkLit :: Literal -> Maybe Expr
mkLit (LitNumber _ n) = mkI n
-- mkLit (MachInt64  n)    = mkI n
-- mkLit (MachWord   n)    = mkI n
-- mkLit (MachWord64 n)    = mkI n
-- mkLit (LitInteger n _)  = mkI n
mkLit (LitFloat  n)    = mkR n
mkLit (LitDouble n)    = mkR n
mkLit (LitString    s)    = mkS s
mkLit (LitChar   c)    = mkC c
mkLit _                 = Nothing -- ELit sym sort

mkI :: Integer -> Maybe Expr
mkI = Just . ECon . I

mkR :: Rational -> Maybe Expr
mkR                    = Just . ECon . F.R . fromRational

mkS :: ByteString -> Maybe Expr
mkS                    = Just . ESym . SL  . decodeUtf8With lenientDecode

mkC :: Char -> Maybe Expr
mkC                    = Just . ECon . (`F.L` F.charSort)  . repr
  where
    repr               = T.pack . show . Data.Char.ord

ignoreVar :: Id -> Bool
ignoreVar i = simpleSymbolVar i `elem` ["I#", "D#"]

-- | Tries to determine if a 'CoreAlt' maps to one of the 'Integer' type constructors.
isBangInteger :: [C.CoreAlt] -> Bool
isBangInteger [Alt (C.DataAlt s) _ _, Alt (C.DataAlt jp) _ _, Alt (C.DataAlt jn) _ _]
  =  symbol s  == symbol (show 'IS)
  && symbol jp == symbol (show 'IP)
  && symbol jn == symbol (show 'IN)
isBangInteger _ = False

isErasable :: Id -> Bool
isErasable v = F.notracepp msg $ isGhcSplId v && not (isDCId v)
  where
    msg      = "isErasable: " ++ GM.showPpr (v, Ghc.idDetails v)

isGhcSplId :: Id -> Bool
isGhcSplId v = isPrefixOfSym (symbol ("$" :: String)) (simpleSymbolVar v)

isDCId :: Id -> Bool
isDCId v = case Ghc.idDetails v of
  DataConWorkId _ -> True
  DataConWrapId _ -> True
  _               -> False

isANF :: Id -> Bool
isANF      v = isPrefixOfSym (symbol ("lq_anf" :: String)) (simpleSymbolVar v)

isDead :: Id -> Bool
isDead     = isDeadOcc . occInfo . Ghc.idInfo

class Simplify a where
  simplify :: Bool -> a -> a
  inline   :: (Id -> Bool) -> a -> a

  normalize :: Bool -> a -> a
  normalize allowTC = inline_preds . inline_anf . simplify allowTC
   where
    inline_preds = inline (eqType boolTy . GM.expandVarType)
    inline_anf   = inline isANF

instance Simplify C.CoreExpr where
  simplify _ e@(C.Var _)
    = e
  simplify _ e@(C.Lit _)
    = e
  simplify allowTC (C.App e (C.Type _))
    = simplify allowTC e
  simplify allowTC (C.App e (C.Var dict))  | (if allowTC then GM.isEmbeddedDictVar else isErasable) dict
    = simplify allowTC e
  simplify allowTC (C.App (C.Lam x e) _)   | isDead x
    = simplify allowTC e
  simplify allowTC (C.App e1 e2)
    = C.App (simplify allowTC e1) (simplify allowTC e2)
  simplify allowTC (C.Lam x e) | isTyVar x
    = simplify allowTC e
  simplify allowTC (C.Lam x e) | (if allowTC then GM.isEmbeddedDictVar else isErasable) x
    = simplify allowTC e
  simplify allowTC (C.Lam x e)
    = C.Lam x (simplify allowTC e)
  simplify allowTC (C.Let (C.NonRec x _) e) | (if allowTC then GM.isEmbeddedDictVar else isErasable) x
    = simplify allowTC e
  simplify allowTC (C.Let (C.Rec xes) e)    | all ((if allowTC then GM.isEmbeddedDictVar else isErasable) . fst) xes
    = simplify allowTC e
  simplify allowTC (C.Let xes e)
    = C.Let (simplify allowTC xes) (simplify allowTC e)
  simplify allowTC (C.Case e x _t alts@[Alt _ _ ee,_,_]) | isBangInteger alts
  -- XXX(matt): seems to be for debugging?
    = -- Misc.traceShow ("To simplify allowTC case") $
       sub (M.singleton x (simplify allowTC e)) (simplify allowTC ee)
  simplify allowTC (C.Case e x t alts)
    = C.Case (simplify allowTC e) x t (filter (not . isPatErrorAlt) (simplify allowTC <$> alts))
  simplify allowTC (C.Cast e c)
    = C.Cast (simplify allowTC e) c
  simplify allowTC (C.Tick _ e)
    = simplify allowTC e
  simplify _ (C.Coercion c)
    = C.Coercion c
  simplify _ (C.Type t)
    = C.Type t

  inline p (C.Let (C.NonRec x ex) e) | p x
                               = sub (M.singleton x (inline p ex)) (inline p e)
  inline p (C.Let xes e)       = C.Let (inline p xes) (inline p e)
  inline p (C.App e1 e2)       = C.App (inline p e1) (inline p e2)
  inline p (C.Lam x e)         = C.Lam x (inline p e)
  inline p (C.Case e x t alts) = C.Case (inline p e) x t (inline p <$> alts)
  inline p (C.Cast e c)        = C.Cast (inline p e) c
  inline p (C.Tick t e)        = C.Tick t (inline p e)
  inline _ (C.Var x)           = C.Var x
  inline _ (C.Lit l)           = C.Lit l
  inline _ (C.Coercion c)      = C.Coercion c
  inline _ (C.Type t)          = C.Type t


instance Simplify C.CoreBind where
  simplify allowTC (C.NonRec x e) = C.NonRec x (simplify allowTC e)
  simplify allowTC (C.Rec xes)    = C.Rec (fmap (simplify allowTC) <$> xes )

  inline p (C.NonRec x e) = C.NonRec x (inline p e)
  inline p (C.Rec xes)    = C.Rec (fmap (inline p) <$> xes)

instance Simplify C.CoreAlt where
  simplify allowTC (Alt c xs e) = Alt c xs (simplify allowTC e)
    -- where xs   = F.tracepp _msg xs0
    --      _msg = "isCoVars? " ++ F.showpp [(x, isCoVar x, varType x) | x <- xs0]
  inline p (Alt c xs e) = Alt c xs (inline p e)
