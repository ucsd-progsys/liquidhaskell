{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-} 
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE TupleSections          #-}

module Language.Haskell.Liquid.CoreToLogic ( 

  coreToDef , mkLit, runToLogic, LError(..), 
  logicType, 
  strengthenResult

  ) where

import GHC hiding (Located)
import Var
import Type 

import qualified CoreSyn as C
import Literal
import IdInfo


import TysWiredIn


import Control.Applicative 

import Language.Fixpoint.Misc
import Language.Fixpoint.Names (dropModuleNames, isPrefixOfSym)
import Language.Fixpoint.Types hiding (Def, R, simplify)
import qualified Language.Fixpoint.Types as F
import Language.Haskell.Liquid.GhcMisc hiding (isDictionary)
import Language.Haskell.Liquid.GhcPlay
import Language.Haskell.Liquid.Types    hiding (GhcInfo(..), GhcSpec (..))
import Language.Haskell.Liquid.WiredIn
import Language.Haskell.Liquid.RefType


import qualified Data.HashMap.Strict as M

import Data.Monoid

import Debug.Trace (trace)


logicType :: (Reftable r) => Type -> RRType r
logicType τ = fromRTypeRep $ t{ty_res = res}
  where 
    t   = toRTypeRep $ ofType τ 
    res = mkResType $ ty_res t

    mkResType t 
     | isBool t  = propType
     | otherwise = t

isBool (RApp (RTyCon{rtc_tc = c}) _ _ _) = c == boolTyCon
isBool _ = False

{- strengthenResult type: the refinement depends on whether the result type is a Bool or not:

CASE1: measure f@logic :: X -> Prop <=> f@haskell :: x:X -> {v:Bool | (Prop v) <=> (f@logic x)} 

CASE2: measure f@logic :: X -> Y    <=> f@haskell :: x:X -> {v:Y    | v = (f@logic x)} 
-}

strengthenResult :: Var -> SpecType
strengthenResult v
  | isBool res
  = fromRTypeRep $ rep{ty_res = res `strengthen` r}
  | otherwise
  = fromRTypeRep $ rep{ty_res = res `strengthen` r'}
  where rep = toRTypeRep t
        res = ty_res rep
        r'  = U (exprReft (EApp f [EVar x]))         mempty mempty
        r   = U (propReft (PBexp $ EApp f [EVar x])) mempty mempty
        x   = safeHead "strengthenResult" $ ty_binds rep
        f   = dummyLoc $ dropModuleNames $ simplesymbol v
        t   = (ofType $ varType v) :: SpecType

simplesymbol = symbol . getName

newtype LogicM a = LM (Either a LError)

data LError = LE String

instance Monad LogicM where
	return = LM . Left
	(LM (Left x))  >>= f = f x
	(LM (Right x)) >>= _ = LM (Right x)

instance Functor LogicM where
	fmap f (LM (Left x))  = LM $ Left $ f x
	fmap _ (LM (Right x)) = LM $ Right x

instance Applicative LogicM where
	pure = LM . Left

	(LM (Left f) ) <*> (LM (Left x))  = LM $ Left (f x)
	(LM (Right f)) <*> (LM (Left _))  = LM $ Right f
	(LM (Left _) ) <*> (LM (Right x)) = LM $ Right x
	(LM (Right _)) <*> (LM (Right x)) = LM $ Right x

throw :: String -> LogicM a
throw = LM . Right . LE

runToLogic (LM x) = x

coreToDef :: LocSymbol -> Var -> C.CoreExpr ->  LogicM [Def DataCon]
coreToDef x _ e = go $ inline_preds $ simplify e
  where
    go (C.Lam _  e) = go e
    go (C.Tick _ e) = go e
    go (C.Case _ _ t alts) 
      | eqType t boolTy = mapM goalt_prop alts
      | otherwise       = mapM goalt      alts
    go _                = throw "Measure Functions should have a case at top level"

    goalt ((C.DataAlt d), xs, e) = ((Def x d (symbol <$> xs)) . E) <$> coreToLogic (trace ("ToLogic" ++ show x) e)
    goalt alt = throw $ "Bad alternative" ++ showPpr alt

    goalt_prop ((C.DataAlt d), xs, e) = ((Def x d (symbol <$> xs)) . P) <$> coreToPred (trace ("ToPred" ++ show x) e)
    goalt_prop alt = throw $ "Bad alternative" ++ showPpr alt

    inline_preds = inline (eqType boolTy . varType)



coreToPred :: C.CoreExpr -> LogicM Pred
coreToPred (C.Let b p)  = subst1 <$> coreToPred p <*>  makesub b
coreToPred (C.Tick _ p) = coreToPred p
coreToPred (C.App (C.Var v) e) | ignoreVar v = coreToPred e
coreToPred (C.Var x)
  | x == falseDataConId
  = return PFalse
  | x == trueDataConId
  = return PTrue
coreToPred p@(C.App _ _) = toPredApp p  
coreToPred e
  = PBexp <$> coreToLogic e
-- coreToPred e                  
--  = throw ("Cannot transform to Logical Predicate:\t" ++ showPpr e)


coreToLogic :: C.CoreExpr -> LogicM Expr
coreToLogic (C.Let b e)  = subst1 <$> coreToLogic e <*>  makesub b
coreToLogic (C.Tick _ e) = coreToLogic e
coreToLogic (C.App (C.Var v) e) | ignoreVar v = coreToLogic e
coreToLogic (C.Lit l)            
  = case mkLit l of 
     Nothing -> throw $ "Bad Literal in measure definition" ++ showPpr l
     Just i -> return i
coreToLogic (C.Var x)           = return $ EVar $ symbol x
coreToLogic e@(C.App _ _)       = toLogicApp e 
coreToLogic e                   = throw ("Cannot transform to Logic:\t" ++ showPpr e)


toPredApp :: C.CoreExpr -> LogicM Pred
toPredApp p 
  = do let (f, es) = splitArgs p
       f'         <- tosymbol f
       go f' es
  where
    go f [e1, e2]
      | Just rel <- M.lookup (val f) brels 
      = PAtom rel <$> (coreToLogic e1) <*> (coreToLogic e2)
    go f [e]
      | val f == symbol ("not" :: String)
      = PNot <$>  coreToPred e
    go f es
      | val f == symbol ("or" :: String)
      = POr <$> mapM coreToPred es
      | val f == symbol ("and" :: String)
      = PAnd <$> mapM coreToPred es
      | otherwise
      = (PBexp . (EApp f)) <$> mapM coreToLogic es

toLogicApp :: C.CoreExpr -> LogicM Expr
toLogicApp e   
  =  do let (f, es) = splitArgs e
        args       <- mapM coreToLogic es
        (`makeApp` args) <$> tosymbol f

makeApp f [e1, e2] | Just op <- M.lookup (val f) bops
  = EBin op e1 e2

makeApp f args 
  = EApp f args

brels :: M.HashMap Symbol Brel
brels = M.fromList [ (symbol ("==" :: String), Eq)
                   , (symbol ("/=" :: String), Ne)
                   , (symbol (">=" :: String), Ge)
                   , (symbol (">" :: String) , Gt)
                   , (symbol ("<=" :: String), Le)
                   , (symbol ("<" :: String) , Lt)
                   ]

bops :: M.HashMap Symbol Bop
bops = M.fromList [ (symbol ("+" :: String), Plus)
                  , (symbol ("-" :: String), Minus)
                  , (symbol ("*" :: String), Times)
                  , (symbol ("/" :: String), Div)
                  , (symbol ("%" :: String), Mod)
                  ] 


splitArgs e = (f, reverse es)
 where
    (f, es) = go e

    go (C.App (C.Var i) e) | ignoreVar i       = go e
    go (C.App f (C.Var v)) | isDictionary v    = go f
    go (C.App f e) = (f', e:es) where (f', es) = go f
    go f           = (f, [])

tosymbol (C.Var x) = return $ dummyLoc $ simpleSymbolVar x
tosymbol  e        = throw ("Bad Measure Definition:\n" ++ showPpr e ++ "\t cannot be applied")

makesub (C.NonRec x e) =  (symbol x,) <$> coreToLogic e
makesub  _             = throw "Cannot make Logical Substitution of Recursive Definitions"

mkLit :: Literal -> Maybe Expr
mkLit (MachInt    n)   = mkI n
mkLit (MachInt64  n)   = mkI n
mkLit (MachWord   n)   = mkI n
mkLit (MachWord64 n)   = mkI n
mkLit (MachFloat  n)   = mkR n
mkLit (MachDouble n)   = mkR n
mkLit (LitInteger n _) = mkI n
mkLit _                = Nothing -- ELit sym sort
mkI                    = Just . ECon . I  
mkR                    = Just . ECon . F.R . fromRational

ignoreVar i = simpleSymbolVar i `elem` ["I#"]


simpleSymbolVar  = dropModuleNames . symbol . showPpr . getName

isDictionary v   = isPrefixOfSym (symbol ("$" :: String)) (simpleSymbolVar v)

isDead = isDeadOcc . occInfo . idInfo

class Simplify a where
  simplify :: a -> a 
  inline   :: (Id -> Bool) -> a -> a

instance Simplify C.CoreExpr where
  simplify e@(C.Var _) 
    = e
  simplify e@(C.Lit _) 
    = e
  simplify (C.App e (C.Type _))                        
    = simplify e
  simplify (C.App e (C.Var dict))  | isDictionary dict 
    = simplify e
  simplify (C.App (C.Lam x e) _)   | isDead x          
    = simplify e
  simplify (C.App e1 e2) 
    = C.App (simplify e1) (simplify e2)
  simplify (C.Lam x e) | isTyVar x 
    = simplify e
  simplify (C.Lam x e) 
    = C.Lam x (simplify e)
  simplify (C.Let xes e) 
    = C.Let (simplify xes) (simplify e)
  simplify (C.Case e x t alts) 
    = C.Case (simplify e) x t (simplify <$> alts)
  simplify (C.Cast e _)    
    = simplify e
  simplify (C.Tick _ e) 
    = simplify e
  simplify (C.Coercion c)
    = C.Coercion c
  simplify (C.Type t)
    = C.Type t  

  inline p (C.Let (C.NonRec x ex) e) | p x
                               = sub (M.singleton x (inline p ex)) e
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
  simplify (C.NonRec x e) = C.NonRec x (simplify e)
  simplify (C.Rec xes)    = C.Rec (mapSnd simplify <$> xes )

  inline p (C.NonRec x e) = C.NonRec x (inline p e)
  inline p (C.Rec xes)    = C.Rec (mapSnd (inline p) <$> xes)

instance Simplify C.CoreAlt where
  simplify (c, xs, e) = (c, xs, simplify e) 

  inline p (c, xs, e) = (c, xs, inline p e)

