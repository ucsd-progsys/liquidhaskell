{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE TupleSections          #-}

module Language.Haskell.Liquid.Transforms.CoreToLogic
  ( coreToDef
  , coreToFun
  , coreToLogic
  , mkLit, mkI, mkS
  , runToLogic
  , runToLogicWithBoolBinds
  , logicType
  , strengthenResult
  , strengthenResult'
  , weakenResult
  , normalize
  ) where

import           Data.ByteString                       (ByteString)
import           GHC                                   hiding (Located, exprType)
import           Prelude                               hiding (error)
import           Type
import           Language.Haskell.Liquid.GHC.TypeRep
-- import qualified Id 
import qualified Var
import qualified TyCon 
import           Coercion
import qualified Pair
-- import qualified Text.Printf as Printf
import qualified CoreSyn                               as C
import           Literal
import           IdInfo
import qualified Data.List                             as L
import           Data.Maybe                            (listToMaybe) 
import qualified Data.Text                             as T
import qualified Data.Char 
import qualified Text.Printf as Printf 
import           Data.Text.Encoding
import           Data.Text.Encoding.Error
import           TysWiredIn
import           Name                                  (getSrcSpan)
import           Control.Monad.State
import           Control.Monad.Except
import           Control.Monad.Identity
import qualified Language.Fixpoint.Misc                as Misc 
import           Language.Fixpoint.Types               hiding (panic, Error, R, simplify)
import qualified Language.Fixpoint.Types               as F
import qualified Language.Haskell.Liquid.GHC.Misc      as GM
import           Language.Haskell.Liquid.Bare.Misc
import           Language.Haskell.Liquid.Bare.Env
import           Language.Haskell.Liquid.GHC.Play
import           Language.Haskell.Liquid.Types         hiding (GhcInfo(..), GhcSpec (..), LM)
import           Language.Haskell.Liquid.Types.RefType


import qualified Data.HashMap.Strict                   as M

logicType :: (Reftable r) => Type -> RRType r
logicType τ      = fromRTypeRep $ t { ty_binds = bs, ty_args = as, ty_refts = rs}
  where
    t            = toRTypeRep $ ofType τ
    (bs, as, rs) = unzip3 $ dropWhile (isClassType . Misc.snd3) $ zip3 (ty_binds t) (ty_args t) (ty_refts t)

{- | [NOTE:strengthenResult type]: the refinement depends on whether the result type is a Bool or not:
      CASE1: measure f@logic :: X -> Bool <=> f@haskell :: x:X -> {v:Bool | v <=> (f@logic x)}
     CASE2: measure f@logic :: X -> Y    <=> f@haskell :: x:X -> {v:Y    | v = (f@logic x)}
 -}

strengthenResult :: Var -> SpecType
strengthenResult v = fromRTypeRep $ rep{ty_res = res `strengthen` r , ty_binds = xs}
  where
    r              = MkUReft (mkR (mkEApp f (mkA <$> vxs))) mempty mempty
    rep            = toRTypeRep t
    res            = ty_res rep
    xs             = intSymbol (symbol ("x" :: String)) <$> [1..length $ ty_binds rep]
    vxs            = dropWhile (isClassType . snd) $ zip xs (ty_args rep)
    f              = dummyLoc (symbol v)
    t              = ofType (GM.expandVarType v) :: SpecType
    mkA            = EVar . fst 
    mkR            = if isBool res then propReft else exprReft 

-- | Refine types of measures: keep going until you find the last data con!
--   this code is a hack! we refine the last data constructor,
--   it got complicated to support both
--   1. multi parameter measures     (see tests/pos/HasElem.hs)
--   2. measures returning functions (fromReader :: Reader r a -> (r -> a) )
--   TODO: SIMPLIFY by dropping support for multi parameter measures

strengthenResult' :: Var -> SpecType
strengthenResult' v = go mkT [] [1..] t
  where 
    mkR | boolRes   = propReft 
        | otherwise = exprReft  
    mkT xs          = MkUReft (mkR $ mkEApp f (EVar <$> reverse xs)) mempty mempty
    f               = dummyLoc (symbol v) 
    t               = ofType (GM.expandVarType v) :: SpecType
    boolRes         =  isBool $ ty_res $ toRTypeRep t 

    go f args i (RAllT a t)      = RAllT a $ go f args i t
    go f args i (RAllP p t)      = RAllP p $ go f args i t
    go f args i (RFun x t1 t2 r)
     | isClassType t1           = RFun x t1 (go f args i t2) r
    go f args i t@(RFun _ t1 t2 r)
     | hasRApps t               = RFun x' t1 (go f (x':args) (tail i) t2) r
                                       where x' = intSymbol (symbol ("x" :: String)) (head i)
    go f args _ t                = t `strengthen` f args

    hasRApps (RFun _ t1 t2 _) = hasRApps t1 || hasRApps t2
    hasRApps (RApp {})        = True
    hasRApps _                = False
    
-- | 'weakenResult foo t' drops the singleton constraint `v = foo x y` 
--   that is added, e.g. for measures in /strengthenResult'. 
--   This should only be used _when_ checking the body of 'foo' 
--   where the output, is, by definition, equal to the singleton.
weakenResult :: Var -> SpecType -> SpecType 
weakenResult v t = F.notracepp msg t'
  where 
    msg          = "weakenResult v =" ++ GM.showPpr v ++ " t = " ++ showpp t
    t'           = fromRTypeRep $ rep { ty_res = mapExprReft weaken (ty_res rep) } 
    rep          = toRTypeRep t
    weaken x     = pAnd . filter ((Just vE /=) . isSingletonExpr x) . conjuncts 
    vE           = mkEApp vF xs
    xs           = EVar . fst <$> dropWhile (isClassType . snd) xts 
    xts          = zip (ty_binds rep) (ty_args rep)
    vF           = dummyLoc (symbol v)

type LogicM = ExceptT Error (StateT LState Identity)

data LState = LState
  { lsSymMap  :: LogicMap
  , lsError   :: String -> Error
  , lsEmb     :: TCEmb TyCon
  , lsBools   :: [Var]
  , lsDCMap   :: DataConMap
  }

throw :: String -> LogicM a
throw str = do
  fmkError  <- lsError <$> get
  throwError $ fmkError str

getState :: LogicM LState
getState = get

runToLogic
  :: TCEmb TyCon -> LogicMap -> DataConMap -> (String -> Error)
  -> LogicM t -> Either Error t
runToLogic = runToLogicWithBoolBinds []

runToLogicWithBoolBinds
  :: [Var] -> TCEmb TyCon -> LogicMap -> DataConMap -> (String -> Error)
  -> LogicM t -> Either Error t
runToLogicWithBoolBinds xs tce lmap dm ferror m
  = evalState (runExceptT m) $ LState
      { lsSymMap = lmap
      , lsError  = ferror
      , lsEmb    = tce
      , lsBools  = xs
      , lsDCMap  = dm
      }

coreAltToDef :: (Reftable r) => LocSymbol -> Var -> [Var] -> Var -> Type -> [C.CoreAlt] 
             -> LogicM [Def (Located (RRType r)) DataCon]
coreAltToDef x z zs y t alts  
  | not (null litAlts) = measureFail x "Cannot lift definition with literal alternatives" 
  | otherwise          = do 
      d1s <- F.notracepp "coreAltDefs-1" <$> mapM (mkAlt x cc myArgs z) dataAlts 
      d2s <- F.notracepp "coreAltDefs-2" <$>     mkDef x cc myArgs z  defAlts defExpr 
      return (d1s ++ d2s)
  where 
    myArgs   = reverse zs
    cc       = if eqType t boolTy then P else E 
    defAlts  = GM.defaultDataCons (GM.expandVarType y) (Misc.fst3 <$> alts)
    defExpr  = listToMaybe [ e |   (C.DEFAULT  , _, e) <- alts ]
    dataAlts =             [ a | a@(C.DataAlt _, _, _) <- alts ]
    litAlts  =             [ a | a@(C.LitAlt _, _, _) <- alts ]

    -- mkAlt :: LocSymbol -> (Expr -> Body) -> [Var] -> Var -> (C.AltCon, [Var], C.CoreExpr)
    mkAlt x ctor args dx (C.DataAlt d, xs, e)
      = Def x (toArgs id args) d (Just $ varRType dx) (toArgs Just xs) 
      . ctor 
      . (`subst1` (F.symbol dx, F.mkEApp (GM.namedLocSymbol d) (F.eVar <$> xs))) 
     <$> coreToLg e
    mkAlt _ _ _ _ alt 
      = throw $ "Bad alternative" ++ GM.showPpr alt

    mkDef x ctor args dx (Just dtss) (Just e) = do  
      eDef   <- ctor <$> coreToLg e
      let ys  = toArgs id args
      let dxt = Just (varRType dx)
      return  [ Def x ys d dxt (defArgs x ts) eDef | (d, ts) <- dtss ]
    
    mkDef _ _ _ _ _ _ = 
      return [] 

toArgs :: Reftable r => (Located (RRType r) -> b) -> [Var] -> [(Symbol, b)]
toArgs f args = [(symbol x, f $ varRType x) | x <- args]

defArgs :: Monoid r => LocSymbol -> [Type] -> [(Symbol, Maybe (Located (RRType r)))]
defArgs x     = zipWith (\i t -> (defArg i, defRTyp t)) [0..] 
  where 
    defArg    = tempSymbol (val x)
    defRTyp   = Just . F.atLoc x . ofType

coreToDef :: Reftable r => LocSymbol -> Var -> C.CoreExpr
          -> LogicM [Def (Located (RRType r)) DataCon]
coreToDef x _ e                   = F.notracepp "CORE-TO-DEF" <$> (go [] $ inlinePreds $ simplify e)
  where
    go args   (C.Lam  x e)        = go (x:args) e
    go args   (C.Tick _ e)        = go args e
    go (z:zs) (C.Case _ y t alts) = coreAltToDef x z zs y t alts 
    go (z:zs) e                   
      | Just t <- isMeasureArg z  = coreAltToDef x z zs z t [(C.DEFAULT, [], e)]
    go _ _                        = measureFail x "Does not have a case-of at the top-level" 

    inlinePreds   = inline (eqType boolTy . GM.expandVarType)

measureFail       :: LocSymbol -> String -> a
measureFail x msg = panic sp e 
  where sp        = Just (GM.fSrcSpan x)
        e         = Printf.printf "Cannot create measure '%s': %s" (F.showpp x) msg
    

-- | 'isMeasureArg x' returns 'Just t' if 'x' is a valid argument for a measure.
isMeasureArg :: Var -> Maybe Type 
isMeasureArg x 
  | Just tc <- tcMb 
  , TyCon.isAlgTyCon tc = F.notracepp "isMeasureArg" $ Just t 
  | otherwise           = Nothing 
  where 
    t                   = GM.expandVarType x  
    tcMb                = tyConAppTyCon_maybe t


varRType :: (Reftable r) => Var -> Located (RRType r)
varRType = GM.varLocInfo ofType

coreToFun :: LocSymbol -> Var -> C.CoreExpr ->  LogicM ([Var], Either Expr Expr)
coreToFun _ _v e = go [] $ normalize e
  where
    go acc (C.Lam x e)  | isTyVar    x = go acc e
    go acc (C.Lam x e)  | isErasable x = go acc e
    go acc (C.Lam x e)  = go (x:acc) e
    go acc (C.Tick _ e) = go acc e
    go acc e            = (reverse acc,) . Right . F.tracepp "CORE-TO-LOGIC" <$> coreToLg e
    

instance Show C.CoreExpr where
  show = GM.showPpr

coreToLogic :: C.CoreExpr -> LogicM Expr
coreToLogic cb = coreToLg (normalize cb)


coreToLg :: C.CoreExpr -> LogicM Expr
coreToLg (C.Let b e)
  = subst1 <$> coreToLg e <*>  makesub b
coreToLg (C.Tick _ e)          = coreToLg e
coreToLg (C.App (C.Var v) e)
  | ignoreVar v                = coreToLg e
coreToLg (C.Var x)
  | x == falseDataConId        = return PFalse
  | x == trueDataConId         = return PTrue
  | otherwise                  = (lsSymMap <$> getState) >>= eVarWithMap x
coreToLg e@(C.App _ _)         = toPredApp e
coreToLg (C.Case e b _ alts)
  | eqType (GM.expandVarType b) boolTy  = checkBoolAlts alts >>= coreToIte e
coreToLg (C.Lam x e)           = do p     <- coreToLg e
                                    tce   <- lsEmb <$> getState
                                    return $ ELam (symbol x, typeSort tce (GM.expandVarType x)) p
coreToLg (C.Case e b _ alts)   = do p <- coreToLg e
                                    casesToLg b p alts
coreToLg (C.Lit l)             = case mkLit l of
                                   Nothing -> throw $ "Bad Literal in measure definition" ++ GM.showPpr l
                                   Just i  -> return i
coreToLg (C.Cast e c)          = do (s, t) <- coerceToLg c
                                    e'     <- coreToLg   e
                                    return (ECoerc s t e')
coreToLg e                     = throw ("Cannot transform to Logic:\t" ++ GM.showPpr e)




coerceToLg :: Coercion -> LogicM (Sort, Sort)
coerceToLg = typeEqToLg . coercionTypeEq

coercionTypeEq :: Coercion -> (Type, Type)
coercionTypeEq co
  | Pair.Pair s t <- -- GM.tracePpr ("coercion-type-eq-1: " ++ GM.showPpr co) $
                       coercionKind co
  = (s, t)

typeEqToLg :: (Type, Type) -> LogicM (Sort, Sort)
typeEqToLg (s, t) = do
  tce   <- gets lsEmb
  let tx = typeSort tce . expandTypeSynonyms
  return $ F.notracepp "TYPE-EQ-TO-LOGIC" (tx s, tx t)

checkBoolAlts :: [C.CoreAlt] -> LogicM (C.CoreExpr, C.CoreExpr)
checkBoolAlts [(C.DataAlt false, [], efalse), (C.DataAlt true, [], etrue)]
  | false == falseDataCon, true == trueDataCon
  = return (efalse, etrue)

checkBoolAlts [(C.DataAlt true, [], etrue), (C.DataAlt false, [], efalse)]
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
    go []          = panic (Just (getSrcSpan v)) "Unexpected empty cases in casesToLg"
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
    isDefault (c,_,_)   = c == C.DEFAULT 

altToLg :: Expr -> C.CoreAlt -> LogicM (C.AltCon, Expr)
altToLg de (a@(C.DataAlt d), xs, e) = do 
  p  <- coreToLg e
  dm <- gets lsDCMap
  let su = mkSubst $ concat [ dataConProj dm de d x i | (x, i) <- zip xs [1..]]
  return (a, subst su p)

altToLg _ (a, _, e)
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
toPredApp p = go . Misc.mapFst opSym . splitArgs $ p
  where
    opSym = fmap GM.dropModuleNames . tomaybesymbol
    go (Just f, [e1, e2])
      | Just rel <- M.lookup f brels
      = PAtom rel <$> coreToLg e1 <*> coreToLg e2
    go (Just f, [e])
      | f == symbol ("not" :: String)
      = PNot <$>  coreToLg e
    go (Just f, [e1, e2])
      | f == symbol ("||" :: String)
      = POr <$> mapM coreToLg [e1, e2]
      | f == symbol ("&&" :: String)
      = PAnd <$> mapM coreToLg [e1, e2]
      | f == symbol ("==>" :: String)
      = PImp <$> coreToLg e1 <*> coreToLg e2
    go (Just f, es)
      | f == symbol ("or" :: String)
      = POr  <$> mapM coreToLg es
      | f == symbol ("and" :: String)
      = PAnd <$> mapM coreToLg es
    go (_, _)
      = toLogicApp p

toLogicApp :: C.CoreExpr -> LogicM Expr
toLogicApp e = do
  let (f, es) = splitArgs e
  case f of
    C.Var _ -> do args <- mapM coreToLg es
                  lmap <- lsSymMap <$> getState
                  def  <- (`mkEApp` args) <$> tosymbol f
                  ((\x -> makeApp def lmap x args) <$> (tosymbol' f))
    _       -> do (fe : args) <- mapM coreToLg (f:es)
                  return $ foldl EApp fe args

makeApp :: Expr -> LogicMap -> Located Symbol-> [Expr] -> Expr
makeApp _ _ f [e] | val f == symbol ("GHC.Num.negate" :: String)
  = ENeg e

makeApp _ _ f [e1, e2] | Just op <- M.lookup (val f) bops
  = EBin op e1 e2

makeApp def lmap f es
  = eAppWithMap lmap f es def
  -- where msg = "makeApp f = " ++ show f ++ " es = " ++ show es ++ " def = " ++ show def

eVarWithMap :: Id -> LogicMap -> LogicM Expr
eVarWithMap x lmap = do
  f'     <- tosymbol' (C.Var x :: C.CoreExpr)
  -- let msg = "eVarWithMap x = " ++ show x ++ " f' = " ++ show f'
  return $ eAppWithMap lmap f' [] (varExpr x)

varExpr :: Var -> Expr
varExpr x
  | isPolyCst t = mkEApp (dummyLoc s) []
  | otherwise   = EVar s
  where
    t           = GM.expandVarType x
    s           = symbol x

isPolyCst :: Type -> Bool
isPolyCst (ForAllTy _ t) = isCst t
isPolyCst _              = False

isCst :: Type -> Bool
isCst (ForAllTy _ t) = isCst t
isCst (FunTy _ _)    = False
isCst _              = True


brels :: M.HashMap Symbol Brel
brels = M.fromList [ (symbol ("==" :: String), Eq)
                   , (symbol ("/=" :: String), Ne)
                   , (symbol (">=" :: String), Ge)
                   , (symbol (">" :: String) , Gt)
                   , (symbol ("<=" :: String), Le)
                   , (symbol ("<" :: String) , Lt)
                   ]

bops :: M.HashMap Symbol Bop
bops = M.fromList [ (numSymbol "+", Plus)
                  , (numSymbol "-", Minus)
                  , (numSymbol "*", Times)
                  , (numSymbol "/", Div)
                  , (numSymbol "%", Mod)
                  ]
  where
    numSymbol :: String -> Symbol
    numSymbol =  symbol . (++) "GHC.Num."

splitArgs :: C.Expr t -> (C.Expr t, [C.Arg t])
splitArgs e = (f, reverse es)
 where
    (f, es) = go e

    go (C.App (C.Var i) e) | ignoreVar i       = go e
    go (C.App f (C.Var v)) | isErasable v      = go f
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
makesub (C.NonRec x e) =  (symbol x,) <$> coreToLg e
makesub  _             = throw "Cannot make Logical Substitution of Recursive Definitions"

mkLit :: Literal -> Maybe Expr
mkLit (MachInt    n)   = mkI n
mkLit (MachInt64  n)   = mkI n
mkLit (MachWord   n)   = mkI n
mkLit (MachWord64 n)   = mkI n
mkLit (MachFloat  n)   = mkR n
mkLit (MachDouble n)   = mkR n
mkLit (LitInteger n _) = mkI n
mkLit (MachStr    s)   = mkS s
mkLit (MachChar   c)   = mkC c 
mkLit _                = Nothing -- ELit sym sort

mkI :: Integer -> Maybe Expr
mkI                    = Just . ECon . I

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

isErasable :: Id -> Bool
isErasable v = F.notracepp msg $ isGhcSplId v && not (isDCId v) 
  where 
    msg      = "isErasable: " ++ GM.showPpr (v, Var.idDetails v)

isGhcSplId :: Id -> Bool
isGhcSplId v = isPrefixOfSym (symbol ("$" :: String)) (simpleSymbolVar v)

isDCId :: Id -> Bool
isDCId v = case Var.idDetails v of 
  DataConWorkId _ -> True 
  DataConWrapId _ -> True 
  _               -> False 

isANF :: Id -> Bool
isANF      v = isPrefixOfSym (symbol ("lq_anf" :: String)) (simpleSymbolVar v)

isDead :: Id -> Bool
isDead     = isDeadOcc . occInfo . Var.idInfo

class Simplify a where
  simplify :: a -> a
  inline   :: (Id -> Bool) -> a -> a

  normalize :: a -> a
  normalize = inline_preds . inline_anf . simplify
   where
    inline_preds = inline (eqType boolTy . GM.expandVarType)
    inline_anf   = inline isANF

instance Simplify C.CoreExpr where
  simplify e@(C.Var _)
    = e
  simplify e@(C.Lit _)
    = e
  simplify (C.App e (C.Type _))
    = simplify e
  simplify (C.App e (C.Var dict))  | isErasable dict
    = simplify e
  simplify (C.App (C.Lam x e) _)   | isDead x
    = simplify e
  simplify (C.App e1 e2)
    = C.App (simplify e1) (simplify e2)
  simplify (C.Lam x e) | isTyVar x
    = simplify e
  simplify (C.Lam x e) | isErasable x
    = simplify e
  simplify (C.Lam x e)
    = C.Lam x (simplify e)
  simplify (C.Let (C.NonRec x _) e) | isErasable x
    = simplify e
  simplify (C.Let (C.Rec xes) e)    | all (isErasable . fst) xes
    = simplify e
  simplify (C.Let xes e)
    = C.Let (simplify xes) (simplify e)
  simplify (C.Case e x t alts)
    = C.Case (simplify e) x t (filter (not . isUndefined) (simplify <$> alts))
  simplify (C.Cast e c)
    = C.Cast (simplify e) c
  simplify (C.Tick _ e)
    = simplify e
  simplify (C.Coercion c)
    = C.Coercion c
  simplify (C.Type t)
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

isUndefined :: (t, t1, C.Expr t2) -> Bool
isUndefined (_, _, e) = isUndefinedExpr e
  where
   -- auto generated undefined case: (\_ -> (patError @type "error message")) void
   isUndefinedExpr (C.App (C.Var x) _) | (show x) `elem` perrors = True
   isUndefinedExpr (C.Let _ e) = isUndefinedExpr e
   -- otherwise
   isUndefinedExpr _ = False

   perrors = ["Control.Exception.Base.patError"]


instance Simplify C.CoreBind where
  simplify (C.NonRec x e) = C.NonRec x (simplify e)
  simplify (C.Rec xes)    = C.Rec (Misc.mapSnd simplify <$> xes )

  inline p (C.NonRec x e) = C.NonRec x (inline p e)
  inline p (C.Rec xes)    = C.Rec (Misc.mapSnd (inline p) <$> xes)

instance Simplify C.CoreAlt where
  simplify (c, xs, e) = (c, xs, simplify e)
    -- where xs   = F.tracepp _msg xs0
    --      _msg = "isCoVars? " ++ F.showpp [(x, isCoVar x, varType x) | x <- xs0]
  inline p (c, xs, e) = (c, xs, inline p e)
