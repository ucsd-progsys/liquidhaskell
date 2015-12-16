{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE TupleSections #-}

module Language.Haskell.Liquid.Bare.OfType (
    ofBareType
  , ofMeaSort
  , ofBSort

  , ofBPVar

  , mkSpecType
  , mkSpecType'
  ) where

import BasicTypes
import Name
import TyCon hiding (synTyConRhs_maybe)
import Type (expandTypeSynonyms)
import TysWiredIn

import Control.Applicative
import Control.Monad.Reader hiding (forM)
import Control.Monad.State hiding (forM)
import Data.Maybe (fromMaybe)
import Data.Monoid
import Data.Traversable (forM)
import Text.Parsec.Pos
import Text.Printf

import qualified Control.Exception as Ex
import qualified Data.HashMap.Strict as M

import Language.Fixpoint.Misc (errorstar)
import Language.Fixpoint.Types (Expr(..), Reftable, Symbol, meet, mkSubst, subst, symbol)

import Language.Haskell.Liquid.GHC.Misc
import Language.Haskell.Liquid.Misc (secondM)
import Language.Haskell.Liquid.Types.RefType
import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.Types.Bounds

import Language.Haskell.Liquid.Bare.Env
import Language.Haskell.Liquid.Bare.Expand
import Language.Haskell.Liquid.Bare.Lookup
import Language.Haskell.Liquid.Bare.Resolve
-- import Language.Haskell.Liquid.Bare.RefToLogic

--------------------------------------------------------------------------------

ofBareType :: SourcePos -> BareType -> BareM SpecType
ofBareType l
  = ofBRType expandRTAliasApp (resolve l <=< expandReft)

ofMeaSort :: BareType -> BareM SpecType
ofMeaSort
  = ofBRType failRTAliasApp return

ofBSort :: BSort -> BareM RSort
ofBSort
  = ofBRType failRTAliasApp return

--------------------------------------------------------------------------------

ofBPVar :: BPVar -> BareM RPVar
ofBPVar
  = mapM_pvar ofBSort

mapM_pvar :: (Monad m) => (a -> m b) -> PVar a -> m (PVar b)
mapM_pvar f (PV x t v txys)
  = do t'    <- forM t f
       txys' <- mapM (\(t, x, y) -> liftM (, x, y) (f t)) txys
       return $ PV x t' v txys'

--------------------------------------------------------------------------------

mkSpecType :: SourcePos -> BareType -> BareM SpecType
mkSpecType l t
  = mkSpecType' l (ty_preds $ toRTypeRep t) t

mkSpecType' :: SourcePos -> [PVar BSort] -> BareType -> BareM SpecType
mkSpecType' l πs t
  = ofBRType expandRTAliasApp resolveReft t
  where
    resolveReft
      = (resolve l <=< expandReft) . txParam subvUReft (uPVar <$> πs) t


txParam f πs t = f (txPvar (predMap πs t))

txPvar :: M.HashMap Symbol UsedPVar -> UsedPVar -> UsedPVar
txPvar m π = π { pargs = args' }
  where args' | not (null (pargs π)) = zipWith (\(_,x ,_) (t,_,y) -> (t, x, y)) (pargs π') (pargs π)
              | otherwise            = pargs π'
        π'    = fromMaybe (errorstar err) $ M.lookup (pname π) m
        err   = "Bare.replaceParams Unbound Predicate Variable: " ++ show π

predMap πs t = M.fromList [(pname π, π) | π <- πs ++ rtypePredBinds t]

rtypePredBinds = map uPVar . ty_preds . toRTypeRep

--------------------------------------------------------------------------------

ofBRType :: (PPrint r, UReftable r)
         => (SourcePos -> RTAlias RTyVar SpecType -> [BRType r] -> r -> BareM (RRType r))
         -> (r -> BareM r)
         -> BRType r
         -> BareM (RRType r)
ofBRType appRTAlias resolveReft
  = go
  where
    go t@(RApp _ _ _ _)
      = do aliases <- (typeAliases . rtEnv) <$> get
           goRApp aliases t
    go (RAppTy t1 t2 r)
      = RAppTy <$> go t1 <*> go t2 <*> resolveReft r
    go (RFun x t1 t2 r)
      =  do env <- get
            goRFun (bounds env) x t1 t2 r
    go (RVar a r)
      = RVar (symbolRTyVar a) <$> resolveReft r
    go (RAllT a t)
      = RAllT (symbolRTyVar a) <$> go t
    go (RAllP a t)
      = RAllP <$> ofBPVar a <*> go t
    go (RAllS x t)
      = RAllS x <$> go t
    go (RAllE x t1 t2)
      = RAllE x <$> go t1 <*> go t2
    go (REx x t1 t2)
      = REx x <$> go t1 <*> go t2
    go (RRTy e r o t)
      = RRTy <$> mapM (secondM go) e <*> resolveReft r <*> pure o <*> go t
    go (RHole r)
      = RHole <$> resolveReft r
    go (RExprArg (Loc l l' e))
      = RExprArg . Loc l l' <$> resolve l e

    go_ref (RPropP ss r)
      = RPropP <$> mapM go_syms ss <*> resolveReft r
    go_ref (RProp ss t)
      = RProp <$> mapM go_syms ss <*> go t
    go_ref (RHProp _ _)
      = errorstar "TODO:EFFECTS:ofBRType"

    go_syms
      = secondM ofBSort

    goRFun bounds _ (RApp c ps' _ _) t _ | Just bnd <- M.lookup c bounds
      = do let (ts', ps) = splitAt (length $ tyvars bnd) ps'
           ts <- mapM go ts'
           makeBound bnd ts [x | RVar x _ <- ps] <$> go t
    goRFun _ x t1 t2 r
      = RFun x <$> go t1 <*> go t2 <*> resolveReft r

    goRApp aliases (RApp (Loc l _ c) ts _ r) | Just rta <- M.lookup c aliases
      = appRTAlias l rta ts =<< resolveReft r
    goRApp _ (RApp lc ts rs r)
      =  do let l = loc lc
            r'  <- resolveReft r
            lc' <- Loc l l <$> matchTyCon lc (length ts)
            rs' <- mapM go_ref rs
            ts' <- mapM go ts
            bareTCApp r' lc' rs' ts'
    goRApp _ _ = errorstar "This cannot happen"


matchTyCon :: LocSymbol -> Int -> BareM TyCon
matchTyCon lc@(Loc _ _ c) arity
  | isList c && arity == 1
    = return listTyCon
  | isTuple c
    = return $ tupleTyCon BoxedTuple arity
  | otherwise
    = lookupGhcTyCon lc

--------------------------------------------------------------------------------

failRTAliasApp :: SourcePos -> RTAlias RTyVar SpecType -> [BRType r] -> r -> BareM (RRType r)
failRTAliasApp l rta _ _
  = Ex.throw err
  where
    err :: Error
    err = ErrIllegalAliasApp (sourcePosSrcSpan l) (pprint $ rtName rta) (sourcePosSrcSpan $ rtPos rta)


expandRTAliasApp :: SourcePos -> RTAlias RTyVar SpecType -> [BareType] -> RReft -> BareM SpecType
expandRTAliasApp l rta args r
  | length args == length αs + length εs
    = do ts <- mapM (ofBareType l)                   $ take (length αs) args
         es <- mapM (resolve l . exprArg (show err)) $ drop (length αs) args
         let tsu = zipWith (\α t -> (α, toRSort t, t)) αs ts
         let esu = mkSubst $ zip (symbol <$> εs) es
         return $ subst esu . (`strengthen` r) . subsTyVars_meet tsu $ rtBody rta
  | otherwise
    = Ex.throw err
  where
    αs        = rtTArgs rta
    εs        = rtVArgs rta
    err       :: Error
    err       = ErrAliasApp (sourcePosSrcSpan l) (length args) (pprint $ rtName rta) (sourcePosSrcSpan $ rtPos rta) (length αs + length εs)

-- | exprArg converts a tyVar to an exprVar because parser cannot tell
-- HORRIBLE HACK To allow treating upperCase X as value variables X
-- e.g. type Matrix a Row Col = List (List a Row) Col

exprArg _   (RExprArg e)
  = val e
exprArg _   (RVar x _)
  = EVar (symbol x)
exprArg _   (RApp x [] [] _)
  = EVar (symbol x)
exprArg msg (RApp f ts [] _)
  = EApp (symbol <$> f) (exprArg msg <$> ts)
exprArg msg (RAppTy (RVar f _) t _)
  = EApp (dummyLoc $ symbol f) [exprArg msg t]
exprArg msg z
  = errorstar $ printf "Unexpected expression parameter: %s in %s" (show z) msg

--------------------------------------------------------------------------------

bareTCApp r (Loc l _ c) rs ts | Just rhs <- synTyConRhs_maybe c
  = do when (realTcArity c < length ts) (Ex.throw err)
       return $ tyApp (subsTyVars_meet su $ ofType rhs) (drop nts ts) rs r
    where
       tvs = tyConTyVarsDef c
       su  = zipWith (\a t -> (rTyVar a, toRSort t, t)) tvs ts
       nts = length tvs

       err :: Error
       err = ErrAliasApp (sourcePosSrcSpan l) (length ts) (pprint c) (getSrcSpan c) (realTcArity c)

-- TODO expandTypeSynonyms here to
bareTCApp r (Loc _ _ c) rs ts | isFamilyTyCon c && isTrivial t
  = return $ expandRTypeSynonyms $ t `strengthen` r
  where t = rApp c ts rs mempty

bareTCApp r (Loc _ _ c) rs ts
  = return $ rApp c ts rs r

tyApp (RApp c ts rs r) ts' rs' r' = RApp c (ts ++ ts') (rs ++ rs') (r `meet` r')
tyApp t                []  []  r  = t `strengthen` r
tyApp _                 _  _   _  = errorstar $ "Bare.Type.tyApp on invalid inputs"

expandRTypeSynonyms :: (PPrint r, Reftable r) => RRType r -> RRType r
expandRTypeSynonyms = ofType . expandTypeSynonyms . toType
