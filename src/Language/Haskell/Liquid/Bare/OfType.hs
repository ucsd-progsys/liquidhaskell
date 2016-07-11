{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE TupleSections #-}

module Language.Haskell.Liquid.Bare.OfType (
    ofBareType
  , ofMeaSort
  , ofBSort
  , ofBPVar
  , mkLSpecType
  , mkSpecType'
  ) where

import Prelude hiding (error)
import BasicTypes
import Name
import Kind (isKindVar)
import TyCon hiding (synTyConRhs_maybe)
import Type (expandTypeSynonyms)
import TysWiredIn


import Control.Monad.Reader hiding (forM)
import Control.Monad.State hiding (forM)
import Data.Maybe (fromMaybe)

import Data.Traversable (forM)
import Text.Parsec.Pos
import Text.Printf

import Text.PrettyPrint.HughesPJ

import qualified Control.Exception as Ex
import qualified Data.HashMap.Strict as M

-- import Language.Fixpoint.Misc (traceShow)
import Language.Fixpoint.Types (atLoc, Expr(..), Reftable, Symbol, meet, mkSubst,
                                subst, symbol, symbolString, mkEApp)


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
  = mapMPvar ofBSort

mapMPvar :: (Monad m) => (a -> m b) -> PVar a -> m (PVar b)
mapMPvar f (PV x t v txys)
  = do t'    <- forM t f
       txys' <- mapM (\(t, x, y) -> liftM (, x, y) (f t)) txys
       return $ PV x t' v txys'

--------------------------------------------------------------------------------
mkLSpecType :: Located BareType -> BareM (Located SpecType)
mkLSpecType t = atLoc t <$> mkSpecType (loc t) (val t)

mkSpecType :: SourcePos -> BareType -> BareM SpecType
mkSpecType l t = mkSpecType' l (ty_preds $ toRTypeRep t) t

mkSpecType' :: SourcePos -> [PVar BSort] -> BareType -> BareM SpecType
mkSpecType' l πs t
  = ofBRType expandRTAliasApp resolveReft t
  where
    resolveReft
      = (resolve l <=< expandReft) . txParam l subvUReft (uPVar <$> πs) t


txParam :: SourcePos
        -> ((UsedPVar -> UsedPVar) -> t) -> [UsedPVar] -> RType c tv r -> t
txParam l f πs t = f (txPvar l (predMap πs t))

txPvar :: SourcePos -> M.HashMap Symbol UsedPVar -> UsedPVar -> UsedPVar
txPvar l m π = π { pargs = args' }
  where args' | not (null (pargs π)) = zipWith (\(_,x ,_) (t,_,y) -> (t, x, y)) (pargs π') (pargs π)
              | otherwise            = pargs π'
        π'    = fromMaybe (panic (Just $ sourcePosSrcSpan l) err) $ M.lookup (pname π) m
        err   = "Bare.replaceParams Unbound Predicate Variable: " ++ show π

predMap :: [UsedPVar] -> RType c tv r -> M.HashMap Symbol UsedPVar
predMap πs t = M.fromList [(pname π, π) | π <- πs ++ rtypePredBinds t]

rtypePredBinds :: RType c tv r -> [UsedPVar]
rtypePredBinds = map uPVar . ty_preds . toRTypeRep

--------------------------------------------------------------------------------

ofBRType :: (PPrint r, UReftable r, SubsTy RTyVar (RType RTyCon RTyVar ()) r, SubsTy BTyVar BSort r)
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
      = RVar (bareRTyVar a) <$> resolveReft r
    go (RAllT a t)
      = RAllT (dropTyVarInfo $ mapTyVarValue bareRTyVar a) <$> go t
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

    go_ref (RProp ss (RHole r))
      = rPropP <$> mapM go_syms ss <*> resolveReft r
    go_ref (RProp ss t)
      = RProp <$> mapM go_syms ss <*> go t


    go_syms
      = secondM ofBSort

    goRFun bounds _ (RApp c ps' _ _) t _
      | Just bnd <- M.lookup (btc_tc c) bounds
      = do let (ts', ps) = splitAt (length $ tyvars bnd) ps'
           ts <- mapM go ts'
           makeBound bnd ts [x | RVar (BTV x) _ <- ps] <$> go t
    goRFun _ x t1 t2 r
      = RFun x <$> go t1 <*> go t2 <*> resolveReft r

    goRApp aliases (RApp tc ts _ r)
      | Loc l _ c <- btc_tc tc
      , Just rta <- M.lookup c aliases
      = appRTAlias l rta ts =<< resolveReft r
    goRApp _ (RApp tc ts rs r)
      =  do let lc = btc_tc tc
            let l = loc lc
            r'  <- resolveReft r
            lc' <- Loc l l <$> matchTyCon lc (length ts)
            rs' <- mapM go_ref rs
            ts' <- mapM go ts
            bareTCApp r' lc' rs' ts'
    goRApp _ _ = impossible Nothing "goRApp failed through to final case"


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
  | Just errmsg <- isOK
    = Ex.throw errmsg  
  | otherwise
    = do ts <- mapM (ofBareType l) $ take (length αs) args
         es <- mapM (resolve l . exprArg (symbolString $ rtName rta)) $ drop (length αs) args
         let tsu = zipWith (\α t -> (α, toRSort t, t)) αs ts
         let esu = mkSubst $ zip (symbol <$> εs) es
         return $ subst esu . (`strengthen` r) . subsTyVars_meet tsu $ rtBody rta

  where
    αs        = rtTArgs rta
    εs        = rtVArgs rta
    err       :: Doc -> Error
    err       = ErrAliasApp (sourcePosSrcSpan l) 
                            (pprint $ rtName rta) 
                            (sourcePosSrcSpan $ rtPos rta) 


    isOK :: Maybe Error
    isOK
      | length args /= length targs + length eargs
      = Just $ err (text "Expects" <+> (pprint $ length αs) <+> text "type arguments and then" <+> (pprint $ length εs) <+> text "expression arguments, but is given" <+> (pprint $ length args))
      | length args /= length αs + length εs
      = Just $ err (text "Expects" <+> (pprint $ length αs) <+> text "type arguments and " <+> (pprint $ length εs) <+> text "expression arguments, but is given" <+> (pprint $ length args))
      | length αs /= length targs, not (null eargs)
      = Just $ err (text "Expects" <+> (pprint $ length αs) <+> text "type arguments before expression arguments")
--  Many expression arguments are parsed like type arguments
{- 
      | length αs /= length targs      
      = Just $ err (text "Expects" <+> (pprint $ length αs) <+> text "type arguments but is given" <+> (pprint $ length targs))
      | length εs /= length eargs
      = Just $ err (text "Expects" <+> (pprint $ length εs) <+> text "expression arguments but is given" <+> (pprint $ length eargs))
-} 
      | otherwise
      = Nothing

    notIsRExprArg (RExprArg _) = False 
    notIsRExprArg _            = True

    targs = takeWhile notIsRExprArg args
    eargs = dropWhile notIsRExprArg args





-- | exprArg converts a tyVar to an exprVar because parser cannot tell
-- HORRIBLE HACK To allow treating upperCase X as value variables X
-- e.g. type Matrix a Row Col = List (List a Row) Col

exprArg :: (PrintfArg t1)  => t1 -> BareType -> Expr
exprArg _   (RExprArg e)
  = val e
exprArg _   (RVar x _)
  = EVar (symbol x)
exprArg _   (RApp x [] [] _)
  = EVar (symbol x)
exprArg msg (RApp f ts [] _)
  = mkEApp (symbol <$> btc_tc f) (exprArg msg <$> ts)
exprArg msg (RAppTy (RVar f _) t _)
  = mkEApp (dummyLoc $ symbol f) [exprArg msg t]
exprArg msg z
  = panic Nothing $ printf "Unexpected expression parameter: %s in %s" (show z) msg
    -- FIXME: Handle this error much better!

--------------------------------------------------------------------------------

bareTCApp :: (Monad m, PPrint r, Reftable r, SubsTy RTyVar RSort r)
          => r
          -> Located TyCon
          -> [RTProp RTyCon RTyVar r]
          -> [RType RTyCon RTyVar r]
          -> m (RType RTyCon RTyVar r)
bareTCApp r (Loc l _ c) rs ts | Just rhs <- synTyConRhs_maybe c
  = do when (realTcArity c < length ts) (Ex.throw err)
       return $ tyApp (subsTyVars_meet su $ ofType rhs) (drop nts ts) rs r
    where
       tvs = filter (not . isKindVar) $ tyConTyVarsDef c
       su  = zipWith (\a t -> (rTyVar a, toRSort t, t)) tvs ts
       nts = length tvs

       err :: Error
       err = ErrAliasApp (sourcePosSrcSpan l) (pprint c) (getSrcSpan c) 
                         (text "Expects " <+> (pprint $ realTcArity c) <+> text "arguments, but is given" <+> (pprint $ length ts))

-- TODO expandTypeSynonyms here to
bareTCApp r (Loc _ _ c) rs ts | isFamilyTyCon c && isTrivial t
  = return (expandRTypeSynonyms $ t `strengthen` r)
  where t = rApp c ts rs mempty

bareTCApp r (Loc _ _ c) rs ts
  = return $ rApp c ts rs r

tyApp :: Reftable r
      => RType c tv r
      -> [RType c tv r] -> [RTProp c tv r] -> r -> RType c tv r
tyApp (RApp c ts rs r) ts' rs' r' = RApp c (ts ++ ts') (rs ++ rs') (r `meet` r')
tyApp t                []  []  r  = t `strengthen` r
tyApp _                 _  _   _  = panic Nothing $ "Bare.Type.tyApp on invalid inputs"

expandRTypeSynonyms :: (PPrint r, Reftable r, SubsTy RTyVar (RType RTyCon RTyVar ()) r) => RRType r -> RRType r
expandRTypeSynonyms = ofType . expandTypeSynonyms . toType
