{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Language.Haskell.Liquid.Bare.Axiom (makeAxiom) where

import CoreSyn
import DataCon
import Id
import Name
import Type hiding (isFunTy)
import Var

import Prelude hiding (mapM)
import Control.Arrow ((&&&))
import Control.Applicative ((<$>), (<*>))
import Control.Monad hiding (forM, mapM)
import Control.Monad.Error hiding (Error, forM, mapM)
import Control.Monad.State hiding (forM, mapM)
import Data.Bifunctor
import Data.Maybe
import Data.Char (toUpper)
import Data.Monoid
import Data.Traversable (forM, mapM)
import Text.PrettyPrint.HughesPJ (text)
import Text.Parsec.Pos (SourcePos)

import qualified Data.List as L

import qualified Data.HashMap.Strict as M
import qualified Data.HashSet        as S

import Language.Fixpoint.Misc (mlookup, sortNub, snd3, traceShow)

import Language.Fixpoint.Names
import Language.Fixpoint.Types (Expr(..))
import Language.Fixpoint.Sort (isFirstOrder)
import qualified Language.Fixpoint.Types as F
import Language.Haskell.Liquid.GhcMisc (showPpr)
import Language.Haskell.Liquid.RefType
import Language.Haskell.Liquid.CoreToLogic
import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.GhcMisc (getSourcePos, getSourcePosE, sourcePosSrcSpan, isDataConId, dropModuleNames)
import Language.Haskell.Liquid.RefType (dataConSymbol, generalize, ofType, uRType, typeSort)
import Language.Haskell.Liquid.Types hiding (binders)
import Language.Haskell.Liquid.Bounds
import Language.Haskell.Liquid.WiredIn

import qualified Language.Haskell.Liquid.Measure as Ms

import Language.Haskell.Liquid.Bare.Env
import Language.Haskell.Liquid.Bare.Misc       (simpleSymbolVar, hasBoolResult)
import Language.Haskell.Liquid.Bare.Expand
import Language.Haskell.Liquid.Bare.Lookup
import Language.Haskell.Liquid.Bare.OfType
import Language.Haskell.Liquid.Bare.Resolve
import Language.Haskell.Liquid.Bare.RefToLogic

makeAxiom :: LogicMap -> [CoreBind] -> GhcSpec -> Ms.BareSpec -> LocSymbol 
          -> BareM ((Symbol, Located SpecType), [(Var, Located SpecType)], [HAxiom])
makeAxiom lmap cbs _ _ x
  = case filter ((val x `elem`) . map (dropModuleNames . simplesymbol) . binders) cbs of
    (NonRec v def:_)   -> do updateLMap lmap x v
                             return $ traceShow ("makeAxiom NonRec" ++ show def) 
                                      ((val x, makeType v), [(v, makeAssumeType v)], defAxioms v def)
    (Rec [(v, def)]:_) -> do vts <- zipWithM (makeAxiomType lmap x) (reverse $ findAxiomNames x cbs) (defAxioms v def)
                             updateLMap lmap x v -- (reverse $ findAxiomNames x cbs) (defAxioms v def)
                             return ((val x, makeType v), 
                                     ((v, makeAssumeType v): vts), 
                                     defAxioms v def)
    _                  -> throwError $ mkError "Cannot extract measure from haskell function"
  where

    coreToDef' x v def = case runToLogic lmap mkError $ coreToDef x v def of
                            Left l  -> l :: [Def (RRType ()) DataCon] -- return     l
                            Right _ -> error $ "ERROR" -- throwError e

    mkError :: String -> Error
    mkError str = ErrHMeas (sourcePosSrcSpan $ loc x) (val x) (text str)

    makeType v       = x{val = ufType    $ varType v}
    makeAssumeType v = x{val = axiomType x $ varType v}

binders (NonRec x _) = [x]
binders (Rec xes)    = fst <$> xes


updateLMap :: LogicMap -> LocSymbol -> Var -> BareM ()
updateLMap lmap x vv -- v axm@(Axiom (vv, _) xs _ lhs rhs)
  = insertLogicEnv (val x) ys runFun
  where
    nargs = dropWhile isClassType $ ty_args $ toRTypeRep $ ((ofType $ varType vv) :: RRType ())

    ys@[x1, x2] = zipWith (\i _ -> symbol (("x" ++ show i) :: String)) [1..] nargs
    runFun = F.EApp (dummyLoc runFunName) [F.EApp (dummyLoc runFunName) [F.EVar $ val x, F.EVar x1], F.EVar x2]

{-

    t   = fromRTypeRep $ tr{ty_res = res, ty_binds = symbol <$> xs}  
    tr  = toRTypeRep $ ofType $ varType v 
    res = ty_res tr `strengthen` U ref mempty mempty

    llhs = case runToLogic lmap' mkErr (coreToLogic lhs) of 
           Left e -> e 
           Right e -> error $ show e 
    lrhs = case runToLogic lmap' mkErr (coreToLogic rhs) of 
           Left e -> e
           Right e -> error $ show e 

    ref = F.Reft (F.vv_, F.PAtom F.Eq llhs lrhs)


    lmap' = lmap -- M.insert v' (LMap v' ys runFun) lmap


    mkErr s = ErrHMeas (sourcePosSrcSpan $ loc x) (val x) (text s)

    -- mkBinds [] [] = []
    mkBinds (x:xs) (v:vs) = v:mkBinds xs vs
    mkBinds _ _ = []

    v' = val x -- symbol $ showPpr $ getName vv

-}


makeAxiomType :: LogicMap -> LocSymbol -> Var -> HAxiom -> BareM (Var, Located SpecType)
makeAxiomType lmap x v axm@(Axiom (vv, _) xs _ lhs rhs)
  = return $ traceShow ("\n\nTYPESSSS\n\n"  ++ showpp (llhs, lrhs)) (v, x{val = t})
  where
    t   = fromRTypeRep $ tr{ty_res = res, ty_binds = symbol <$> xs}  
    tr  = toRTypeRep $ ofType $ varType v 
    res = ty_res tr `strengthen` U ref mempty mempty

    llhs = case runToLogic lmap' mkErr (coreToLogic lhs) of 
  		     Left e -> e 
  		     Right e -> error $ show e 
    lrhs = case runToLogic lmap' mkErr (coreToLogic rhs) of 
  		     Left e -> e
  		     Right e -> error $ show e 
    ref = F.Reft (F.vv_, F.PAtom F.Eq llhs lrhs)

    nargs = dropWhile isClassType $ ty_args $ toRTypeRep $ ((ofType $ varType vv) :: RRType ())

    ys@[x1, x2] = zipWith (\i _ -> symbol (("x" ++ show i) :: String)) [1..] nargs

    lmap' = lmap -- M.insert v' (LMap v' ys runFun) lmap

    runFun = F.EApp (dummyLoc runFunName) [F.EApp (dummyLoc runFunName) [F.EVar $ val x, F.EVar x1], F.EVar x2]

    mkErr s = ErrHMeas (sourcePosSrcSpan $ loc x) (val x) (text s)

    mkBinds (x:xs) (v:vs) = v:mkBinds xs vs
    mkBinds _ _ = []

    v' = val x -- symbol $ showPpr $ getName vv




findAxiomNames x (NonRec v _ :cbs) | isAxiomName x v = v:findAxiomNames x cbs 
findAxiomNames x (Rec [(v,_)]:cbs) | isAxiomName x v = v:findAxiomNames x cbs 
findAxiomNames x (_:cbs) = findAxiomNames x cbs
findAxiomNames _ [] = []

isAxiomName x v = 
  (("axiom_" ++ symbolString (val x)) `L.isPrefixOf`) (symbolString $ dropModuleNames $ simplesymbol v)


defAxioms v e = go [] e  
  where
  	go bs (Tick _ e) = go bs e
  	go bs (Lam x e) | isTyVar x               = go bs e  
  	go bs (Lam x e) | isClassPred (varType x) = go bs e 
  	go bs (Lam x e) = go (bs++[x]) e 
  	go bs (Case  (Var x) _ _ alts)  = goalt x bs  <$> alts 
  	go _ _ = error "TODO: defAxioms"

  	goalt x bs (DataAlt c, ys, e) = let vs = [b | b<- bs , b /= x] ++ ys in 
                                    Axiom (v, Just c) vs (varType <$> vs) (mkApp bs x c ys) $ simplify e
  	goalt _ _  (LitAlt _,  _,  _) = error "TODO defAxioms: goalt Lit"
  	goalt _ _  (DEFAULT,   _,  _) = error "TODO defAxioms: goalt Def"

  	mkApp bs x c ys = foldl App (Var v) ((\y -> if y == x then (mkConApp c (Var <$> ys)) else Var y)<$> bs)


class Simplifiable a where
	simplify :: a -> a

instance Simplifiable CoreExpr where
  simplify (Tick _ e) = simplify e
  simplify (Lam x e) | isTyVar x = simplify e 
  simplify (Lam x e) | isClassPred (varType x) = simplify e 
  simplify (Lam x e) = Lam x $ simplify e 
  simplify (Let b e) = unANF (simplify b) (simplify e)
  simplify (Case e v t alts) = Case e v t alts 
  simplify (Cast e _) = simplify e 
  simplify (App e (Type _)) = simplify e 
  simplify (App e (Var x)) | isClassPred (varType x) = simplify e 
  simplify (App f e) = App (simplify f) (simplify e)
  simplify e@(Var _) = e 
  simplify e = error ("TODO simplify" ++ show e)

unANF (NonRec x ex) e | L.isPrefixOf "lq_anf" (show x)
  = subst (x, ex) e 
unANF b e = Let b e

instance Simplifiable CoreBind where 
  simplify (NonRec x e) = NonRec x $ simplify e 
  simplify (Rec xes)    = Rec (second simplify <$> xes) 


class Subable a where
  subst :: (Var, CoreExpr) -> a -> a 

instance Subable CoreExpr where
  subst (x, ex) (Var y) | x == y    = ex 
                        | otherwise = Var y
  subst su (App f e) = App (subst su f) (subst su e)  
  subst su (Lam x e) = Lam x (subst su e)
  subst _ _          = error "TODO Subable"

-- | Specification for Haskell function 
axiomType :: LocSymbol -> Type -> SpecType
axiomType s τ = fromRTypeRep $ t{ty_res = res, ty_binds = xs}
  where
    t  = toRTypeRep $ ofType τ
    ys = dropWhile isClassType $ ty_args t
    xs = (\i -> symbol ("x" ++ show i)) <$> [1..(length ys)]
    x  = F.vv_

    res = ty_res t `strengthen` U ref mempty mempty

    ref = F.Reft (x, F.PAtom F.Eq (F.EVar x) (mkApp xs))

    mkApp = F.EApp s . map F.EVar -- foldl runFun (F.EVar $ val s)

    runFun e x = F.EApp (dummyLoc runFunName) [e, F.EVar x]


-- | Type for uninterpreted function that approximated Haskell function into logic
ufType :: (F.Reftable r) => Type -> RRType r
ufType τ = fromRTypeRep $ t{ty_res = res, ty_args = [], ty_binds = [], ty_refts = []}
  where
    t    = toRTypeRep $ ofType τ
    args = dropWhile isClassType $ ty_args t
    res  = mkType args $ ty_res t

    mkType []     tr = tr
    mkType (t:ts) tr = arrowType t $ mkType ts tr

simplesymbol :: CoreBndr -> Symbol
simplesymbol = symbol . getName
