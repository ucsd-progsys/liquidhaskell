{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Language.Haskell.Liquid.Bare.Axiom (makeHaskellAxioms) where

import Prelude hiding (error)
import CoreSyn
import TyCon
-- import DataCon
import Id
import Name
import Type hiding (isFunTy)
import Var
import TypeRep

import Prelude hiding (mapM)

-- import           Control.Monad hiding (forM, mapM)
import           Control.Monad.Except hiding (forM, mapM)
import           Control.Monad.State hiding (forM, mapM)
import           Text.PrettyPrint.HughesPJ (text)
-- import qualified Data.List    as L
import qualified Data.HashSet as S
import           Language.Fixpoint.Misc
import           Language.Fixpoint.Types (Symbol, symbol)

import qualified Language.Haskell.Liquid.Measure as Ms
import qualified Language.Fixpoint.Types as F
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Transforms.CoreToLogic
import           Language.Haskell.Liquid.GHC.Misc
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Bare.Env

--------------------------------------------------------------------------------
makeHaskellAxioms
  :: F.TCEmb TyCon -> [CoreBind] -> Ms.BareSpec -> BareM [ (Var, LocSpecType)]
--------------------------------------------------------------------------------
makeHaskellAxioms tce cbs sp = do
  xtvds <- getReflectDefs sp cbs
  forM_ xtvds $ \(x,_,v,_) -> updateLMapXV x v
  lmap <- logicEnv <$> get
  mapM (makeAxiom tce lmap cbs) xtvds

updateLMapXV :: LocSymbol -> Var -> BareM ()
updateLMapXV x v = do
  updateLMap x x v
  updateLMap (x {val = (symbol . showPpr . getName) v}) x v

getReflectDefs
  :: Ms.BareSpec -> [CoreBind]
  -> BareM [(LocSymbol, Maybe BareType, Var, CoreExpr)]
getReflectDefs sp cbs      = mapM go vds
  where
    xts                    = getReflects sp
    vds                    = [ (x, t, findVarDef (val x) cbs) | (x, t) <- xts ]
    go (x, t, Just (v, e)) = return (x, t, v, e)
    go (x, _, Nothing    ) = throwError $ mkError x "Cannot lift haskell function"

getReflects :: Ms.BareSpec -> [(LocSymbol, Maybe BareType)]
getReflects sp = F.tracepp "REFLECT-ENV2" [ (x, getSig x) | x <- S.toList (Ms.reflects sp) ]
  where
    allSigs    = Ms.asmSigs sp ++ Ms.sigs sp ++ Ms.localSigs sp
    env        = F.tracepp "REFLECT-ENV1" $ F.fromListSEnv [ (dropModuleNames $ val x, val t) | (x, t) <- allSigs ]
    getSig x   = F.lookupSEnv (val x) env

--------------------------------------------------------------------------------
makeAxiom :: F.TCEmb TyCon
          -> LogicMap
          -> [CoreBind]
          -> (LocSymbol, Maybe BareType, Var, CoreExpr)
          -> BareM (Var, LocSpecType)
--------------------------------------------------------------------------------
makeAxiom tce lmap _cbs (x, mbT, v, def) = do
  -- REFLECT-IMPORTS [] let anames = findAxiomNames x cbs
  -- let haxs   = defAxioms {- REFLECT-IMPORTS anames -} v def
  -- REFLECT-IMPORTS [] vts <- zipWithM (makeAxiomType tce lmap x) (reverse anames) haxs
  insertAxiom v (val x)
  updateLMap x x v
  updateLMap (x{val = (symbol . showPpr . getName) v}) x v
  let (t, _e) = makeAssumeType tce (F.tracepp "makeAX-LMAP" lmap) x mbT v {- REFLECT-IMPORTS anames -}  def
  return (v, t)


mkError :: LocSymbol -> String -> Error
mkError x str = ErrHMeas (sourcePosSrcSpan $ loc x) (pprint $ val x) (text str)

makeSMTAxiom :: LocSymbol -> [(Symbol, F.Sort)] -> F.Expr -> F.Expr
makeSMTAxiom f xs e = F.PAll xs (F.PAtom F.Eq (F.mkEApp f (F.eVar . fst <$> xs)) e)

-- ASKNIKI: what is this function doing?!
makeAssumeType
  :: F.TCEmb TyCon -> LogicMap -> LocSymbol -> Maybe BareType ->  Var -> CoreExpr
  -> (LocSpecType, F.Expr)
makeAssumeType tce lmap x mbT v def
  = (x {val = at `strengthenRes` F.subst su ref},  makeSMTAxiom x xss le )
  where
    -- trep = toRTypeRep t
    t    = ofType $ varType v
    at   = F.tracepp ("axiomType: " ++ msg) $  axiomType x mbT t
    msg  = unwords [showpp x, showpp mbT]
    le   = case runToLogicWithBoolBinds bbs tce lmap mkErr (coreToLogic def') of
             Right e -> e
             Left  e -> panic Nothing $ show e

    ref  = F.Reft (F.vv_, F.PAtom F.Eq (F.EVar F.vv_) le)

    mkErr s = ErrHMeas (sourcePosSrcSpan $ loc x) (pprint $ val x) (text s)

    bbs     = filter isBoolBind xs

    (xs, def') = grapBody $ normalize def
    su = F.mkSubst $ zip (F.symbol     <$> xs) (F.EVar <$> ty_non_dict_binds (toRTypeRep at))
                  ++ zip (simplesymbol <$> xs) (F.EVar <$> ty_non_dict_binds (toRTypeRep at))

    grapBody (Lam x e)  = let (xs, e') = grapBody e in (x:xs, e')
    grapBody (Tick _ e) = grapBody e
    grapBody e          = ([], e)

    xss = [(mkSymbol x t, rTypeSort tce t) | (x, t) <- zip xs (ty_args (toRTypeRep at)), not (isClassType t)]

    mkSymbol x t = if isFunTy t then simplesymbol x else F.symbol x
    ty_non_dict_binds trep = [x | (x, t) <- zip (ty_binds trep) (ty_args trep), not (isClassType t)]

isBoolBind :: Var -> Bool
isBoolBind v = isBool (ty_res $ toRTypeRep ((ofType $ varType v) :: RRType ()))

strengthenRes :: SpecType -> F.Reft -> SpecType
strengthenRes t r = fromRTypeRep $ trep {ty_res = ty_res trep `strengthen` F.ofReft r }
  where
    trep = toRTypeRep t

updateLMap :: LocSymbol -> LocSymbol -> Var -> BareM ()
updateLMap x y vv
  | val x /= val y && isFun (varType vv)
  = insertLogicEnv ("UPDATELMAP: vv =" ++ show vv) x ys (F.eApps (F.EVar $ val y) (F.EVar <$> ys))
  | otherwise
  = return ()
  where
    nargs = dropWhile isClassType $ ty_args trep
    trep  = toRTypeRep ((ofType $ varType vv) :: RRType ())
    ys    = zipWith (\i _ -> symbol ("x" ++ show i)) [1..] nargs

    isFun (FunTy _ _)    = True
    isFun (ForAllTy _ t) = isFun t
    isFun  _             = False

_defAxioms :: Var -> CoreExpr -> [Axiom Var Kind (Expr Var)]
_defAxioms v e = go [] $ normalize e
  where
     go bs (Tick _ e) = go bs e
     go bs (Lam x e) | isTyVar x               = go bs e
     go bs (Lam x e) | isClassPred (varType x) = go bs e
     go bs (Lam x e) = go (bs++[x]) e
     go bs (Case  (Var x) _ _ alts)  = goalt x bs  <$> alts
     go bs e         = [Axiom (v, Nothing) (Nothing {- REFLECT-IMPORTS getSimpleName v -}) bs (varType <$> bs) (foldl App (Var v) (Var <$> bs)) e]

     goalt x bs (DataAlt c, ys, e) = let vs = [b | b<- bs , b /= x] ++ ys in
        Axiom (v, Just c) (Nothing {- REFLECT-IMPORTS getConName v c -}) vs (varType <$> vs) (mkApp bs x c ys) $ normalize e
     goalt _ _  (LitAlt _,  _,  _) = todo Nothing "defAxioms: goalt Lit"
     goalt _ _  (DEFAULT,   _,  _) = todo Nothing "defAxioms: goalt Def"

     mkApp bs x c ys = foldl App (Var v) ((\y -> if y == x then mkConApp c (Var <$> ys) else Var y) <$> bs)

class Subable a where
  subst :: (Var, CoreExpr) -> a -> a

instance Subable Var where
  subst (x, ex) z | x == z, Var y <- ex = y
                  | otherwise           = z

instance Subable CoreExpr where
  subst (x, ex) (Var y)
    | x == y    = ex
    | otherwise = Var y
  subst su (App f e)
    = App (subst su f) (subst su e)
  subst su (Lam x e)
    = Lam x (subst su e)
  subst su (Case e x t alts)
    = Case (subst su e) x t (subst su <$> alts)
  subst su (Let (Rec xes) e)
    = Let (Rec (mapSnd (subst su) <$> xes)) (subst su e)
  subst su (Let (NonRec x ex) e)
    = Let (NonRec x (subst su ex)) (subst su e)
  subst su (Cast e t)
    = Cast (subst su e) t
  subst su (Tick t e)
    = Tick t (subst su e)
  subst _ (Lit l)
    = Lit l
  subst _ (Coercion c)
    = Coercion c
  subst _ (Type t)
    = Type t

instance Subable CoreAlt where
  subst su (c, xs, e) = (c, xs, subst su e)

-- | Specification for Haskell function
axiomType
  :: (TyConable c) => LocSymbol -> Maybe BareType -> RType c tv RReft
  -> RType c tv RReft
axiomType s mbT t = fromRTypeRep (tr {ty_res = res, ty_binds = xs})
  where
    res           = strengthen (ty_res tr) (singletonApp s ys)
    ys            = fst $ unzip $ dropWhile (isClassType . snd) xts
    xts           = safeZip "axiomBinds" xs (ty_args tr)
    xs            = zipWith unDummy bs [1..]
    tr            = toRTypeRep t
    bs            = maybe (ty_binds tr) (ty_binds . toRTypeRep) mbT

unDummy :: F.Symbol -> Int -> F.Symbol
unDummy x i
  | x /= F.dummySymbol = x
  | otherwise          = symbol ("lq" ++ show i)

singletonApp :: F.Symbolic a => LocSymbol -> [a] -> UReft F.Reft
singletonApp s ys = MkUReft r mempty mempty
  where
    r             = F.exprReft (F.mkEApp s (F.eVar <$> ys))
