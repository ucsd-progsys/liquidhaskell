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
  , normalize
  ) where

import           Data.ByteString                       (ByteString)
import           GHC                                   hiding (Located, exprType)
import           Prelude                               hiding (error)
import           Type
import           Language.Haskell.Liquid.GHC.TypeRep
import qualified Var
import           Coercion
import qualified Pair

import qualified CoreSyn                               as C
import           Literal
import           IdInfo

import           Data.Text.Encoding
import           Data.Text.Encoding.Error

import           TysWiredIn

import           Control.Monad.State
import           Control.Monad.Except
import           Control.Monad.Identity
import           Language.Fixpoint.Misc                (snd3, mapSnd, mapFst)
import           Language.Fixpoint.Types               hiding (Error, R, simplify)
import qualified Language.Fixpoint.Types               as F
import           Language.Haskell.Liquid.GHC.Misc
import           Language.Haskell.Liquid.Bare.Misc
import           Language.Haskell.Liquid.Bare.Env
import           Language.Haskell.Liquid.GHC.Play
import           Language.Haskell.Liquid.Types         hiding (GhcInfo(..), GhcSpec (..), LM)
import           Language.Haskell.Liquid.Types.RefType

-- import           Language.Haskell.Liquid.WiredIn
-- import           CoreUtils                                     (exprType)

import qualified Data.HashMap.Strict                   as M

varType :: Var -> Type
varType = expandTypeSynonyms . Var.varType

logicType :: (Reftable r) => Type -> RRType r
logicType τ      = fromRTypeRep $ t { ty_binds = bs, ty_args = as, ty_refts = rs}
  where
    t            = toRTypeRep $ ofType τ
    (bs, as, rs) = unzip3 $ dropWhile (isClassType.snd3) $ zip3 (ty_binds t) (ty_args t) (ty_refts t)

{- [NOTE:strengthenResult type]: the refinement depends on whether the result type is a Bool or not:

   CASE1: measure f@logic :: X -> Prop <=> f@haskell :: x:X -> {v:Bool | (Prop v) <=> (f@logic x)}

   CASE2: measure f@logic :: X -> Y    <=> f@haskell :: x:X -> {v:Y    | v = (f@logic x)}
-}

strengthenResult :: Var -> SpecType
strengthenResult v
  | isBool res
  = -- traceShow ("Type for " ++ showPpr v ++ "\t OF \t" ++ show (ty_binds rep)) $
    fromRTypeRep $ rep{ty_res = res `strengthen` r , ty_binds = xs}
  | otherwise
  = -- traceShow ("Type for " ++ showPpr v ++ "\t OF \t" ++ show (ty_binds rep)) $
    fromRTypeRep $ rep{ty_res = res `strengthen` r', ty_binds = xs}
  where
    rep = toRTypeRep t
    res = ty_res rep
    xs  = intSymbol (symbol ("x" :: String)) <$> [1..length $ ty_binds rep]
    r'  = MkUReft (exprReft (mkEApp f (mkA <$> vxs))) mempty mempty
    r   = MkUReft (propReft (mkEApp f (mkA <$> vxs))) mempty mempty
    vxs = dropWhile (isClassType . snd) $ zip xs (ty_args rep)
    f   = dummyLoc $ symbol v -- dropModuleNames $ simplesymbol v
    t   = (ofType $ varType v) :: SpecType
    mkA = EVar . fst -- if isBool t then EApp (dummyLoc propConName) [(EVar x)] else EVar x


strengthenResult' :: Var -> SpecType
strengthenResult' v
  | isBool $ ty_res $ toRTypeRep t
  = go mkProp [] [1..] t
  | otherwise
  = go mkExpr [] [1..] t
  where f   = dummyLoc $ symbol v -- dropModuleNames $ simplesymbol v
        t   = (ofType $ varType v) :: SpecType

        -- refine types of measures: keep going until you find the last data con!
        -- this code is a hack! we refine the last data constructor,
        -- it got complicated to support both
        -- 1. multi parameter measures     (see tests/pos/HasElem.hs)
        -- 2. measures returning functions (fromReader :: Reader r a -> (r -> a) )
        -- to simplify, drop support for multi parameter measures
        go f args i (RAllT a t)
          = RAllT a $ go f args i t
        go f args i (RAllP p t)
          = RAllP p $ go f args i t
        go f args i (RFun x t1 t2 r)
          | isClassType t1
          = RFun x t1 (go f args i t2) r
        go f args i t@(RFun _ t1 t2 r)
          | hasRApps t
          = let x' = intSymbol (symbol ("x" :: String)) (head i)
            in RFun x' t1 (go f (x':args) (tail i) t2) r
        go f args _ t
          = t `strengthen` f args

        hasRApps (RApp {})        = True
        hasRApps (RFun _ t1 t2 _) = hasRApps t1 || hasRApps t2
        hasRApps _                = False

        mkExpr xs = MkUReft (exprReft $ mkEApp f (EVar <$> reverse xs)) mempty mempty
        mkProp xs = MkUReft (propReft $ mkEApp f (EVar <$> reverse xs)) mempty mempty


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

coreToDef :: Reftable r => LocSymbol -> Var -> C.CoreExpr
          -> LogicM [Def (Located (RRType r)) DataCon]
coreToDef x _ e = go [] $ inline_preds $ simplify e
  where
    go args (C.Lam  x e) = go (x:args) e
    go args (C.Tick _ e) = go args e
    go args (C.Case _ _ t alts)
      | eqType t boolTy  = mapM (goalt_prop (reverse $ tail args) (head args)) alts
      | otherwise        = mapM (goalt      (reverse $ tail args) (head args)) alts
    go _ _               = throw "Measure Functions should have a case at top level"

    goalt args dx (C.DataAlt d, xs, e)
      = Def x (toArgs id args) d (Just $ varRType dx) (toArgs Just xs) . E
        <$> coreToLg e
    goalt _ _ alt
       = throw $ "Bad alternative" ++ showPpr alt

    goalt_prop args dx (C.DataAlt d, xs, e)
      = Def x (toArgs id args) d (Just $ varRType dx) (toArgs Just xs) . P
        <$> coreToLg  e
    goalt_prop _ _ alt
      = throw $ "Bad alternative" ++ showPpr alt

    toArgs f args = [(symbol x, f $ varRType x) | x <- args]

    inline_preds = inline (eqType boolTy . varType)

varRType :: (Reftable r) => Var -> Located (RRType r)
varRType = varLocInfo ofType

coreToFun :: LocSymbol -> Var -> C.CoreExpr ->  LogicM ([Var], Either Expr Expr)
coreToFun _ _v e = go [] $ normalize e
  where
    go acc (C.Lam x e)  | isTyVar    x = go acc e
    go acc (C.Lam x e)  | isErasable x = go acc e
    go acc (C.Lam x e)  = go (x:acc) e
    go acc (C.Tick _ e) = go acc e
    go acc e            = (reverse acc,) . Right <$> coreToLg e

instance Show C.CoreExpr where
  show = showPpr

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
  | eqType (varType b) boolTy  = checkBoolAlts alts >>= coreToIte e
coreToLg (C.Lam x e)           = do p     <- coreToLg e
                                    tce   <- lsEmb <$> getState
                                    return $ ELam (symbol x, typeSort tce (varType x)) p
coreToLg (C.Case e b _ alts)   = do p <- coreToLg e
                                    casesToLg b p alts
coreToLg (C.Lit l)             = case mkLit l of
                                   Nothing -> throw $ "Bad Literal in measure definition" ++ showPpr l
                                   Just i  -> return i
coreToLg (C.Cast e c)          = do (s, t) <- coerceToLg c
                                    e'     <- coreToLg   e
                                    return (ECoerc s t e')
coreToLg e                     = throw ("Cannot transform to Logic:\t" ++ showPpr e)




coerceToLg :: Coercion -> LogicM (Sort, Sort)
coerceToLg = typeEqToLg . coercionTypeEq

coercionTypeEq :: Coercion -> (Type, Type)
coercionTypeEq co
  | Pair.Pair s t <- {- tracePpr ("coercion-type-eq-1: " ++ showPpr co) $ -}
                       coercionKind co
  = (s, t) 

typeEqToLg :: (Type, Type) -> LogicM (Sort, Sort)
typeEqToLg (s, t) = do
  tce   <- gets lsEmb
  return (typeSort tce s, typeSort tce t)

  -- Pair t1 t2 <- coercionKind co
  -- getCoVar_maybe :: Coercion -> Maybe CoVar
  -- getTyVar_maybe :: Type -> Maybe TyVar
  -- coVarTypes :: CoVar -> (Type, Type)

checkBoolAlts :: [C.CoreAlt] -> LogicM (C.CoreExpr, C.CoreExpr)
checkBoolAlts [(C.DataAlt false, [], efalse), (C.DataAlt true, [], etrue)]
  | false == falseDataCon, true == trueDataCon
  = return (efalse, etrue)

checkBoolAlts [(C.DataAlt true, [], etrue), (C.DataAlt false, [], efalse)]
  | false == falseDataCon, true == trueDataCon
  = return (efalse, etrue)
checkBoolAlts alts
  = throw ("checkBoolAlts failed on " ++ showPpr alts)

casesToLg :: Var -> Expr -> [C.CoreAlt] -> LogicM Expr
casesToLg v e alts
  = mapM (altToLg e) alts >>= go
  where
    go :: [(DataCon, Expr)] -> LogicM Expr
    go [(_,p)]     = return (p `subst1` su)
    go ((d,p):dps) = do c <- checkDataCon d e
                        e' <- go dps
                        return (EIte c p e' `subst1` su)
    go []          = throw "Bah"

    su = (symbol v, e)

checkDataCon :: DataCon -> Expr -> LogicM Expr
checkDataCon d e
  = return $ EApp (EVar $ makeDataConChecker d) e

altToLg :: Expr -> C.CoreAlt -> LogicM (DataCon, Expr)
altToLg de (C.DataAlt d, xs, e)
  = do p  <- coreToLg e
       dm <- gets lsDCMap
       let su = mkSubst $ concat [ f dm x i | (x, i) <- zip xs [1..]]
       return (d, subst su p)
  where
    f dm x i = let t = EApp (EVar $ makeDataConSelector (Just dm) d i) de
               in [(symbol x, t), (simplesymbol x, t)]
altToLg _ (C.LitAlt _, _, _)
  = throw "altToLg on Lit"
altToLg _ (C.DEFAULT, _, _)
  = throw ("Cannot reflect functions with Default pattern matching." ++ 
           "\n\t Suggestion: Make sure your function is total and is not pattern matching on integer values.")

coreToIte :: C.CoreExpr -> (C.CoreExpr, C.CoreExpr) -> LogicM Expr
coreToIte e (efalse, etrue)
  = do p  <- coreToLg e
       e1 <- coreToLg efalse
       e2 <- coreToLg etrue
       return $ EIte p e2 e1

toPredApp :: C.CoreExpr -> LogicM Expr
toPredApp p = go . mapFst opSym . splitArgs $ p
  where
    opSym = fmap dropModuleNames . tomaybesymbol
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
    t           = varType x
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
    _      -> throw ("Bad Measure Definition:\n" ++ showPpr e ++ "\t cannot be applied")

tosymbol' :: C.CoreExpr -> LogicM (Located Symbol)
tosymbol' (C.Var x) = return $ dummyLoc $ symbol x -- simpleSymbolVar' x
tosymbol' e        = throw ("Bad Measure Definition:\n" ++ showPpr e ++ "\t cannot be applied")

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
mkLit (MachStr s)      = mkS s
mkLit _                = Nothing -- ELit sym sort

mkI :: Integer -> Maybe Expr
mkI                    = Just . ECon . I

mkR :: Rational -> Maybe Expr
mkR                    = Just . ECon . F.R . fromRational

mkS :: ByteString -> Maybe Expr
mkS                    = Just . ESym . SL  . decodeUtf8With lenientDecode

ignoreVar :: Id -> Bool
ignoreVar i = simpleSymbolVar i `elem` ["I#"]

_simpleSymbolVar' :: Id -> Symbol
_simpleSymbolVar' = simplesymbol --symbol . {- showPpr . -} getName

isErasable :: Id -> Bool
isErasable v = isPrefixOfSym (symbol ("$"      :: String)) (simpleSymbolVar v)

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
    inline_preds = inline (eqType boolTy . varType)
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
  simplify (C.Rec xes)    = C.Rec (mapSnd simplify <$> xes )

  inline p (C.NonRec x e) = C.NonRec x (inline p e)
  inline p (C.Rec xes)    = C.Rec (mapSnd (inline p) <$> xes)

instance Simplify C.CoreAlt where
  simplify (c, xs, e) = (c, xs, simplify e)

  inline p (c, xs, e) = (c, xs, inline p e)
