{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE TupleSections          #-}

module Language.Haskell.Liquid.Transforms.CoreToLogic (

  coreToDef , coreToFun,
  coreToLogic, coreToPred,
  mkLit, runToLogic,
  logicType,
  strengthenResult

  ) where

import GHC hiding (Located)
import Var
import Type
import TypeRep

import qualified CoreSyn   as C
import Literal
import IdInfo

import Data.Text.Encoding

import TysWiredIn

import Control.Applicative

import Language.Fixpoint.Misc (snd3)
import Language.Fixpoint.Types.Names (propConName, isPrefixOfSym)
import Language.Fixpoint.Types hiding (Error, Def, R, simplify)
import qualified Language.Fixpoint.Types as F
import Language.Haskell.Liquid.GHC.Misc
import Language.Haskell.Liquid.GHC.Play
import Language.Haskell.Liquid.Types    hiding (GhcInfo(..), GhcSpec (..))
import Language.Haskell.Liquid.Misc (mapSnd)
import Language.Haskell.Liquid.WiredIn
import Language.Haskell.Liquid.Types.RefType


import qualified Data.HashMap.Strict as M

import Data.Monoid


logicType :: (Reftable r) => Type -> RRType r
logicType τ = fromRTypeRep $ t{ty_res = res, ty_binds = binds, ty_args = args, ty_refts = refts}
  where
    t   = toRTypeRep $ ofType τ
    res = mkResType $ ty_res t
    (binds, args, refts) = unzip3 $ dropWhile (isClassType.snd3) $ zip3 (ty_binds t) (ty_args t) (ty_refts t)


    mkResType t
     | isBool t   = propType
     | otherwise  = t

isBool (RApp (RTyCon{rtc_tc = c}) _ _ _) = c == boolTyCon
isBool _ = False

{- strengthenResult type: the refinement depends on whether the result type is a Bool or not:

CASE1: measure f@logic :: X -> Prop <=> f@haskell :: x:X -> {v:Bool | (Prop v) <=> (f@logic x)}

CASE2: measure f@logic :: X -> Y    <=> f@haskell :: x:X -> {v:Y    | v = (f@logic x)}
-}

strengthenResult :: Var -> SpecType
strengthenResult v
  | isBool res
  = -- traceShow ("Type for " ++ showPpr v ++ "\t OF \t" ++ show (ty_binds rep)) $
    fromRTypeRep $ rep{ty_res = res `strengthen` r, ty_binds = xs}
  | otherwise
  = -- traceShow ("Type for " ++ showPpr v ++ "\t OF \t" ++ show (ty_binds rep)) $
    fromRTypeRep $ rep{ty_res = res `strengthen` r', ty_binds = xs}
  where rep = toRTypeRep t
        res = ty_res rep
        xs  = intSymbol (symbol ("x" :: String)) <$> [1..length $ ty_binds rep]
        r'  = U (exprReft (EApp f (mkA <$> vxs)))         mempty mempty
        r   = U (propReft (PBexp $ EApp f (mkA <$> vxs))) mempty mempty
        vxs = dropWhile (isClassType.snd) $ zip xs (ty_args rep)
        f   = dummyLoc $ dropModuleNames $ simplesymbol v
        t   = (ofType $ varType v) :: SpecType
        mkA = EVar . fst -- if isBool t then EApp (dummyLoc propConName) [(EVar x)] else EVar x


simplesymbol = symbol . getName

newtype LogicM a = LM {runM :: LState -> Either a Error}

data LState = LState { symbolMap :: LogicMap
                     , mkError   :: String -> Error
                     }


instance Monad LogicM where
  return = LM . const . Left
  (LM m) >>= f
    = LM $ \s -> case m s of
                (Left x) -> (runM (f x)) s
                (Right x) -> Right x

instance Functor LogicM where
  fmap f (LM m) = LM $ \s -> case m s of
                              (Left  x) -> Left $ f x
                              (Right x) -> Right x

instance Applicative LogicM where
  pure = LM . const . Left
  (LM f) <*> (LM m)
    = LM $ \s -> case (f s, m s) of
                  (Left f , Left x ) -> Left $ f x
                  (Right f, Left _ ) -> Right f
                  (Left _ , Right x) -> Right x
                  (Right _, Right x) -> Right x

throw :: String -> LogicM a
throw str = LM $ \s -> Right $ (mkError s) str

getState :: LogicM LState
getState = LM $ Left

runToLogic lmap ferror (LM m)
  = m $ LState {symbolMap = lmap, mkError = ferror}

coreToDef :: Reftable r => LocSymbol -> Var -> C.CoreExpr ->  LogicM [Def (RRType r) DataCon]
coreToDef x _ e = go [] $ inline_preds $ simplify e
  where
    go args (C.Lam  x e) = go (x:args) e
    go args (C.Tick _ e) = go args e
    go args (C.Case _ _ t alts)
      | eqType t boolTy  = mapM (goalt_prop (reverse $ tail args) (head args)) alts
      | otherwise        = mapM (goalt      (reverse $ tail args) (head args)) alts
    go _ _               = throw "Measure Functions should have a case at top level"

    goalt args dx ((C.DataAlt d), xs, e)
      = ((Def x (toArgs id args) d (Just $ ofType $ varType dx) (toArgs Just xs)) . E)
        <$> coreToLg e
    goalt _ _ alt
       = throw $ "Bad alternative" ++ showPpr alt

    goalt_prop args dx ((C.DataAlt d), xs, e)
      = ((Def x (toArgs id args) d (Just $ ofType $ varType dx) (toArgs Just xs)) . P)
        <$> coreToPd  e
    goalt_prop _ _ alt
      = throw $ "Bad alternative" ++ showPpr alt

    toArgs f args = [(symbol x, f $ ofType $ varType x) | x <- args]

    inline_preds = inline (eqType boolTy . varType)

coreToFun :: LocSymbol -> Var -> C.CoreExpr ->  LogicM ([Var], Either Pred Expr)
coreToFun _ v e = go [] $ normalize e
  where
    go acc (C.Lam x e)  | isTyVar    x = go acc e
    go acc (C.Lam x e)  | isErasable x = go acc e
    go acc (C.Lam x e)  = go (x:acc) e
    go acc (C.Tick _ e) = go acc e
    go acc e            | eqType rty boolTy
                        = (reverse acc,) . Left  <$> coreToPd e
                        | otherwise
                        = (reverse acc,) . Right <$> coreToLg e


    rty = snd $ splitFunTys $ snd $ splitForAllTys $ varType v

coreToPred :: C.CoreExpr -> LogicM Pred
coreToPred e = coreToPd $ normalize e


coreToPd :: C.CoreExpr -> LogicM Pred
coreToPd (C.Let b p)  = subst1 <$> coreToPd p <*>  makesub b
coreToPd (C.Tick _ p) = coreToPd p
coreToPd (C.App (C.Var v) e) | ignoreVar v = coreToPd e
coreToPd (C.Var x)
  | x == falseDataConId
  = return PFalse
  | x == trueDataConId
  = return PTrue
  | eqType boolTy (varType x)
  = return $ PBexp $ EApp (dummyLoc propConName) [(EVar $ symbol x)]
coreToPd p@(C.App _ _) = toPredApp p
coreToPd e
  = PBexp <$> coreToLg e
-- coreToPd e
--  = throw ("Cannot transform to Logical Predicate:\t" ++ showPpr e)


coreToLogic :: C.CoreExpr -> LogicM Expr
coreToLogic = coreToLg . simplify

coreToLg :: C.CoreExpr -> LogicM Expr
coreToLg (C.Let b e)  = subst1 <$> coreToLg e <*>  makesub b
coreToLg (C.Tick _ e) = coreToLg e
coreToLg (C.App (C.Var v) e) | ignoreVar v = coreToLg e
coreToLg (C.Lit l)
  = case mkLit l of
     Nothing -> throw $ "Bad Literal in measure definition" ++ showPpr l
     Just i -> return i
coreToLg (C.Var x)           = (symbolMap <$> getState) >>= eVarWithMap x
coreToLg e@(C.App _ _)       = toLogicApp e
coreToLg (C.Case e b _ alts) | eqType (varType b) boolTy
  = checkBoolAlts alts >>= coreToIte e
coreToLg e                   = throw ("Cannot transform to Logic:\t" ++ showPpr e)

checkBoolAlts :: [C.CoreAlt] -> LogicM (C.CoreExpr, C.CoreExpr)
checkBoolAlts [(C.DataAlt false, [], efalse), (C.DataAlt true, [], etrue)]
  | false == falseDataCon, true == trueDataCon
  = return (efalse, etrue)
checkBoolAlts [(C.DataAlt true, [], etrue), (C.DataAlt false, [], efalse)]
  | false == falseDataCon, true == trueDataCon
  = return (efalse, etrue)
checkBoolAlts alts
  = throw ("checkBoolAlts failed on " ++ showPpr alts)

coreToIte e (efalse, etrue)
  = do p  <- coreToPd e
       e1 <- coreToLg efalse
       e2 <- coreToLg etrue
       return $ EIte p e2 e1

toPredApp :: C.CoreExpr -> LogicM Pred
toPredApp p
  = do let (f, es) = splitArgs p
       f'         <- tosymbol f
       go f' es
  where
    go f [e1, e2]
      | Just rel <- M.lookup (val f) brels
      = PAtom rel <$> (coreToLg e1) <*> (coreToLg e2)
    go f [e]
      | val f == symbol ("not" :: String)
      = PNot <$>  coreToPd e
    go f [e1, e2]
      | val f == symbol ("||" :: String)
      = POr <$> mapM coreToPd [e1, e2]
      | val f == symbol ("&&" :: String)
      = PAnd <$> mapM coreToPd [e1, e2]
      | val f == symbol ("==>" :: String)
      = PImp <$> coreToPd e1 <*> coreToPd e2
    go f es
      | val f == symbol ("or" :: String)
      = POr <$> mapM coreToPd es
      | val f == symbol ("and" :: String)
      = PAnd <$> mapM coreToPd es
      | otherwise
      = PBexp <$> toLogicApp p

toLogicApp :: C.CoreExpr -> LogicM Expr
toLogicApp e
  =  do let (f, es) = splitArgs e
        args       <- mapM coreToLg es
        lmap       <- symbolMap <$> getState
        def         <- (`EApp` args) <$> tosymbol f
        (\x -> makeApp def lmap x args) <$> tosymbol' f

makeApp :: Expr -> LogicMap -> Located Symbol-> [Expr] -> Expr
makeApp _ _ f [e] | val f == symbol ("GHC.Num.negate" :: String)
  = ENeg e

makeApp _ _ f [e1, e2] | Just op <- M.lookup (val f) bops
  = EBin op e1 e2

makeApp def lmap f es
  = eAppWithMap lmap f es def

eVarWithMap :: Id -> LogicMap -> LogicM Expr
eVarWithMap x lmap
  = do f' <- tosymbol' (C.Var x :: C.CoreExpr)
       return $ eAppWithMap lmap f' [] (eVar x )
  where
    eVar x | isPolyCst $ varType x  = EApp (dummyLoc $ symbol x) []
           | otherwise              = EVar $ symbol x

    isPolyCst (ForAllTy _ t) = isCst t
    isPolyCst _              = False
    isCst     (ForAllTy _ t) = isCst t
    isCst     (FunTy _ _)    = False
    isCst     _              = True


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

splitArgs e = (f, reverse es)
 where
    (f, es) = go e

    go (C.App (C.Var i) e) | ignoreVar i       = go e
    go (C.App f (C.Var v)) | isErasable v    = go f
    go (C.App f e) = (f', e:es) where (f', es) = go f
    go f           = (f, [])

tosymbol (C.Var c) | isDataConId  c = return $ dummyLoc $ symbol c
tosymbol (C.Var x) = return $ dummyLoc $ simpleSymbolVar x
tosymbol  e        = throw ("Bad Measure Definition:\n" ++ showPpr e ++ "\t cannot be applied")

tosymbol' (C.Var x) = return $ dummyLoc $ simpleSymbolVar' x
tosymbol'  e        = throw ("Bad Measure Definition:\n" ++ showPpr e ++ "\t cannot be applied")

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

mkI                    = Just . ECon . I
mkR                    = Just . ECon . F.R . fromRational
mkS                    = Just . ESym . SL  . decodeUtf8

ignoreVar i = simpleSymbolVar i `elem` ["I#"]


simpleSymbolVar  = dropModuleNames . symbol . showPpr . getName
simpleSymbolVar' = symbol . showPpr . getName

isErasable v = isPrefixOfSym (symbol ("$"      :: String)) (simpleSymbolVar v)
isANF      v = isPrefixOfSym (symbol ("lq_anf" :: String)) (simpleSymbolVar v)

isDead     = isDeadOcc . occInfo . idInfo

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
  simplify (C.Cast e _)
    = simplify e
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
