{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Language.Haskell.Liquid.Bare.Axiom (makeHaskellAxioms) where

import Prelude hiding (error)
import CoreSyn
import TyCon
import Id
import Name
import Var
import Language.Haskell.Liquid.GHC.TypeRep

import Prelude hiding (mapM)

import           Control.Monad.Except hiding (forM, mapM)
import           Control.Monad.State hiding (forM, mapM)
import           Text.PrettyPrint.HughesPJ (text)
import qualified Data.HashSet as S
import           Data.Maybe (fromMaybe)
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
  :: F.TCEmb TyCon -> [CoreBind] -> GhcSpec -> Ms.BareSpec
  -> BareM [ (Var, LocSpecType, AxiomEq)]
--------------------------------------------------------------------------------
makeHaskellAxioms tce cbs spec sp = do
  xtvds <- getReflectDefs spec sp cbs
  forM_ xtvds $ \(x,_,v,_) -> updateLMapXV x v
  lmap <- logicEnv <$> get
  mapM (makeAxiom tce lmap cbs) xtvds

updateLMapXV :: LocSymbol -> Var -> BareM ()
updateLMapXV x v = do
  updateLMap x x v
  updateLMap (x {val = (symbol . showPpr . getName) v}) x v

getReflectDefs
  :: GhcSpec -> Ms.BareSpec -> [CoreBind]
  -> BareM [(LocSymbol, Maybe SpecType, Var, CoreExpr)]
getReflectDefs spec sp cbs  = mapM (findVarDefType cbs sigs) xs
  where
    sigs                    = gsTySigs spec
    xs                      = S.toList (Ms.reflects sp)

findVarDefType
  :: [CoreBind] -> [(Var, LocSpecType)] -> LocSymbol
  -> BareM (LocSymbol, Maybe SpecType, Var, CoreExpr)
findVarDefType cbs sigs x = case findVarDef (val x) cbs of
  Just (v, e) -> if F.tracepp ("ISEXPORTED v = " ++ show v) $ isExportedId v
                   then return (x, val <$> lookup v sigs, v, e)
                   else throwError $ mkError x ("Lifted functions must be exported; please export " ++ show v)
  Nothing     -> throwError $ mkError x "Cannot lift haskell function"

--------------------------------------------------------------------------------
makeAxiom :: F.TCEmb TyCon
          -> LogicMap
          -> [CoreBind]
          -> (LocSymbol, Maybe SpecType, Var, CoreExpr)
          -> BareM (Var, LocSpecType, AxiomEq)
--------------------------------------------------------------------------------
makeAxiom tce lmap _cbs (x, mbT, v, def) = do
  insertAxiom v Nothing -- TODO:reflect-datacons (val x)
  updateLMap x x v
  updateLMap (x{val = (symbol . showPpr . getName) v}) x v
  let (t, e) = makeAssumeType tce lmap x mbT v def
  return $ F.tracepp "reflect-datacons:makeAxiom" (v, t, e)

mkError :: LocSymbol -> String -> Error
mkError x str = ErrHMeas (sourcePosSrcSpan $ loc x) (pprint $ val x) (text str)

makeSMTAxiom :: LocSymbol -> [(Symbol, F.Sort)] -> F.Expr -> AxiomEq
makeSMTAxiom f xts e = AxiomEq (val f) xs e (F.PAll xts (F.EEq f_xs e))
  where
    xs               = fst <$> xts
    f_xs             = F.mkEApp f (F.EVar <$> xs)

makeAssumeType
  :: F.TCEmb TyCon -> LogicMap -> LocSymbol -> Maybe SpecType ->  Var -> CoreExpr
  -> (LocSpecType, AxiomEq)
makeAssumeType tce lmap x mbT v def
  = (x {val = at `strengthenRes` F.subst su ref},  makeSMTAxiom x xts le )
  where
    t    = fromMaybe (ofType $ varType v) mbT
    at   = {- F.tracepp ("axiomType: " ++ msg) $ -} axiomType x mbT t
    _msg = unwords [showpp x, showpp mbT]
    le   = F.tracepp "reflect-datacons:le" $ case runToLogicWithBoolBinds bbs tce lmap mkErr (coreToLogic def') of
             Right e -> e
             Left  e -> panic Nothing $ show e

    ref     = F.Reft (F.vv_, F.PAtom F.Eq (F.EVar F.vv_) le)

    mkErr s = ErrHMeas (sourcePosSrcSpan $ loc x) (pprint $ val x) (text s)
    bbs     = filter isBoolBind xs
    (xs, def') = grabBody $ normalize def
    su = F.tracepp "reflect-datacons: subst" $ F.mkSubst
           $ zip (F.symbol     <$> xs) (F.EVar <$> ty_non_dict_binds (toRTypeRep at))
          ++ zip (simplesymbol <$> xs) (F.EVar <$> ty_non_dict_binds (toRTypeRep at))

    xts = zipWith (\x t -> (symbol x, rTypeSort tce t)) xs ts
    ts  = (filter (not . isClassType) (ty_args (toRTypeRep at)))
    -- mkSymbol x _ = F.symbol x
    -- mkSymbol x t = if isFunTy t then simplesymbol x else F.symbol x
    ty_non_dict_binds trep = [x | (x, t) <- zip (ty_binds trep) (ty_args trep), not (isClassType t)]

grabBody :: CoreExpr -> ([Id], CoreExpr)
grabBody (Lam x e)  = (x:xs, e') where (xs, e') = grabBody e
grabBody (Tick _ e) = grabBody e
grabBody e          = ([], e)

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
  :: (TyConable c) => LocSymbol -> Maybe SpecType -> RType c tv RReft
  -> RType c tv RReft
axiomType s _mbT t = fromRTypeRep (tr {ty_res = res, ty_binds = xs})
  where
    res           = strengthen (ty_res tr) (singletonApp s ys)
    ys            = fst $ unzip $ dropWhile (isClassType . snd) xts
    xts           = safeZip "axiomBinds" xs (ty_args tr)
    xs            = zipWith unDummy bs [1..]
    tr            = toRTypeRep t
    bs            = ty_binds tr

unDummy :: F.Symbol -> Int -> F.Symbol
unDummy x i
  | x /= F.dummySymbol = x
  | otherwise          = symbol ("lq" ++ show i)

singletonApp :: F.Symbolic a => LocSymbol -> [a] -> UReft F.Reft
singletonApp s ys = MkUReft r mempty mempty
  where
    r             = F.exprReft (F.mkEApp s (F.eVar <$> ys))
