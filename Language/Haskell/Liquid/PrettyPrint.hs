{-# LANGUAGE FlexibleContexts           #-} 
{-# LANGUAGE FlexibleInstances          #-}

-- | Module with all the printing routines

module Language.Haskell.Liquid.PrettyPrint (
  
  -- * Printing RType
    ppr_rtype
  , showpp
  ) where

import GHC                              (Name)
import Language.Haskell.Liquid.GhcMisc
import Text.PrettyPrint.HughesPJ
import Language.Fixpoint.Types hiding (Predicate)
import Language.Fixpoint.Misc
import Language.Haskell.Liquid.Types
import Language.Fixpoint.Names (dropModuleNames, symSepName, funConName, listConName, tupConName, propConName, boolConName)
import TypeRep          hiding (maybeParen, pprArrowChain)  
import Text.Parsec.Pos  (SourcePos)
import Var              (Var)
import Control.Applicative ((<$>))
import Data.Maybe   (fromMaybe)

instance PPrint Var where
  pprint = pprDoc 

instance PPrint Name where
  pprint = pprDoc 

instance PPrint Type where
  pprint = pprDoc

instance Show Predicate where
  show = showpp


{- 
[hsenv]rjhala@ubuntu:~/research/liquid/liquidhaskell/Language (deepmeasure)$ ack-grep Fixpoint | grep "instance"

Haskell/Liquid/Constraint.hs:156:instance F.Fixpoint CGEnv where
Haskell/Liquid/Constraint.hs:213:instance F.Fixpoint SubC where
Haskell/Liquid/Constraint.hs:219:instance F.Fixpoint WfC where
Haskell/Liquid/Constraint.hs:222:instance F.Fixpoint Cinfo where
Haskell/Liquid/Constraint.hs:436:instance F.Fixpoint CGInfo where 
Haskell/Liquid/Constraint.hs:1196:instance F.Fixpoint REnv where

Haskell/Liquid/PredType.hs:52:instance F.Fixpoint TyConP where
Haskell/Liquid/PredType.hs:60:instance F.Fixpoint DataConP where

Haskell/Liquid/GhcInterface.hs:422:instance Fixpoint GhcSpec where
Haskell/Liquid/GhcInterface.hs:432:instance Fixpoint GhcInfo where 
Haskell/Liquid/GhcInterface.hs:449:instance Fixpoint TargetVars where

Haskell/Liquid/RefType.hs:108:instance Fixpoint Predicate where
Haskell/Liquid/RefType.hs:232:instance Fixpoint () where
Haskell/Liquid/RefType.hs:295:instance Fixpoint String where
Haskell/Liquid/RefType.hs:299:instance Fixpoint Class where
Haskell/Liquid/RefType.hs:303:instance (Eq p, Fixpoint p, TyConable c, Reftable r) => RefTypable p c String r where
Haskell/Liquid/RefType.hs:615:instance Fixpoint RTyVar where
Haskell/Liquid/RefType.hs:623:instance (Reftable s, Reftable  p, Fixpoint t) => Fixpoint (Ref t s (RType a b c p)) where
Haskell/Liquid/RefType.hs:633:instance (Reftable r) => Fixpoint (UReft r) where
Haskell/Liquid/RefType.hs:639:instance Fixpoint (UReft r) => Show (UReft r) where
Haskell/Liquid/RefType.hs:642:instance (Fixpoint a, Fixpoint b, Fixpoint c) => Fixpoint (a, b, c) where
Haskell/Liquid/RefType.hs:645:instance  Fixpoint t => Fixpoint (PVar t) where
Haskell/Liquid/RefType.hs:654:instance (RefTypable p c tv r) => Fixpoint (RType p c tv r) where
Haskell/Liquid/RefType.hs:657:instance Fixpoint (RType p c tv r) => Show (RType p c tv r) where
Haskell/Liquid/RefType.hs:660:instance Fixpoint RTyCon where
Haskell/Liquid/Annotate.hs:280:instance Fixpoint a => Fixpoint (AnnInfo a) where
Haskell/Liquid/Annotate.hs:292:instance Fixpoint Annot where
Haskell/Liquid/Measure.hs:161:instance Fixpoint Body where
Haskell/Liquid/Measure.hs:166:instance Fixpoint a => Fixpoint (BDataCon a) where
Haskell/Liquid/Measure.hs:171:instance Fixpoint a => Fixpoint (Def a) where
Haskell/Liquid/Measure.hs:176:instance (Fixpoint t, Fixpoint a) => Fixpoint (Measure t a) where
Haskell/Liquid/Measure.hs:181:instance (Fixpoint t, Fixpoint a) => Fixpoint (MSpec t a) where
Haskell/Liquid/Measure.hs:185:instance (Fixpoint t , Fixpoint a) => Show (Measure t a) where

-}

---------------------------------------------------------------
-- | Pretty Printing RefType ----------------------------------
---------------------------------------------------------------

-- pprint_rtype    = ppr_rtype $ ppPs ppEnv 

-- ppr_rtype :: (PPrint tv, RefTypable p c tv (), RefTypable p c tv r) 
--           => Bool           -- ^ Whether to print reftPs or not e.g. [a]<...> 
--           -> Prec 
--           -> RType p c tv r 
--           -> Doc

ppr_rtype bb p t@(RAllT _ _)       
  = ppr_forall bb p t
ppr_rtype bb p t@(RAllP _ _)       
  = ppr_forall bb p t
ppr_rtype _ _ (RVar a r)         
  = ppTy r $ pprint a
ppr_rtype bb p (RFun x t t' _)  
  = pprArrowChain p $ ppr_dbind bb FunPrec x t : ppr_fun_tail bb t'
ppr_rtype bb p (RApp c [t] rs r)
  | isList c 
  = ppTy r $ brackets (ppr_rtype bb p t) <> ppReftPs bb rs
ppr_rtype bb p (RApp c ts rs r)
  | isTuple c 
  = ppTy r $ parens (intersperse comma (ppr_rtype bb p <$> ts)) <> ppReftPs bb rs

-- BEXPARSER WHY Does this next case kill the parser for BExp? (e.g. LambdaEval.hs)
-- ppr_rtype bb p (RApp c [] [] r)
--   = ppTy r $ {- parens $ -} ppTycon c

ppr_rtype bb p (RApp c ts rs r)
  = ppTy r $ parens $ ppTycon c <+> ppReftPs bb rs <+> hsep (ppr_rtype bb p <$> ts)

ppr_rtype _ _ (RCls c ts)      
  = ppCls c ts
ppr_rtype bb p t@(REx _ _ _)
  = ppExists bb p t
ppr_rtype bb p t@(RAllE _ _ _)
  = ppAllExpr bb p t
ppr_rtype _ _ (RExprArg e)
  = braces $ pprint e
ppr_rtype bb p (RAppTy t t' r)
  = ppTy r $ ppr_rtype bb p t <+> ppr_rtype bb p t'
ppr_rtype _ _ (ROth s)
  = text $ "???-" ++ s 

-- | From GHC: TypeRep 
-- pprArrowChain p [a,b,c]  generates   a -> b -> c
pprArrowChain :: Prec -> [Doc] -> Doc
pprArrowChain _ []         = empty
pprArrowChain p (arg:args) = maybeParen p FunPrec $
                             sep [arg, sep (map (arrow <+>) args)]

-- | From GHC: TypeRep 
maybeParen :: Prec -> Prec -> Doc -> Doc
maybeParen ctxt_prec inner_prec pretty
  | ctxt_prec < inner_prec = pretty
  | otherwise		       = parens pretty


-- ppExists :: (RefTypable p c tv (), RefTypable p c tv r) => Bool -> Prec -> RType p c tv r -> Doc
ppExists bb p t
  = text "exists" <+> brackets (intersperse comma [ppr_dbind bb TopPrec x t | (x, t) <- zs]) <> dot <> ppr_rtype bb p t'
    where (zs,  t')               = split [] t
          split zs (REx x t t')   = split ((x,t):zs) t'
          split zs t	            = (reverse zs, t)

-- ppAllExpr :: (RefTypable p c tv (), RefTypable p c tv r) => Bool -> Prec -> RType p c tv r -> Doc
ppAllExpr bb p t
  = text "forall" <+> brackets (intersperse comma [ppr_dbind bb TopPrec x t | (x, t) <- zs]) <> dot <> ppr_rtype bb p t'
    where (zs,  t')               = split [] t
          split zs (RAllE x t t') = split ((x,t):zs) t'
          split zs t	            = (reverse zs, t)

ppReftPs bb rs 
  | all isTauto rs   = empty
  | not (ppPs ppEnv) = empty 
  | otherwise        = angleBrackets $ hsep $ punctuate comma $ pprint <$> rs

-- ppr_dbind :: (RefTypable p c tv (), RefTypable p c tv r) => Bool -> Prec -> Symbol -> RType p c tv r -> Doc
ppr_dbind bb p x t 
  | isNonSymbol x || (x == dummySymbol) 
  = ppr_rtype bb p t
  | otherwise
  = pprint x <> colon <> ppr_rtype bb p t

-- ppr_fun_tail :: (RefTypable p c tv (), RefTypable p c tv r) => Bool -> RType p c tv r -> [Doc]
ppr_fun_tail bb (RFun b t t' _)  
  = (ppr_dbind bb FunPrec b t) : (ppr_fun_tail bb t')
ppr_fun_tail bb t
  = [ppr_rtype bb TopPrec t]

-- ppr_forall :: (RefTypable p c tv (), RefTypable p c tv r) => Bool -> Prec -> RType p c tv r -> Doc
ppr_forall bb p t
  = maybeParen p FunPrec $ sep [ ppr_foralls bb αs πs , ppr_cls cls, ppr_rtype bb TopPrec t' ]
  where
    (αs, πs,  ct')         = bkUniv t
    (cls, t')              = bkClass ct'
  
    ppr_foralls False _ _  = empty
    ppr_foralls _    [] [] = empty
    ppr_foralls True αs πs = text "forall" <+> dαs αs <+> dπs bb πs <> dot
    ppr_cls []             = empty
    ppr_cls cs             = (parens $ hsep $ punctuate comma (uncurry ppCls <$> cs)) <+> text "=>"

    dαs αs                 = sep $ pprint <$> αs 
    
    dπs _ []               = empty 
    dπs False _            = empty 
    dπs True πs            = angleBrackets $ intersperse comma $ ppr_pvar_def pprint <$> πs

ppr_pvar_def pprv (PV s t xts) = pprint s <+> dcolon <+> intersperse arrow dargs 
  where 
    dargs = [pprv t | (t,_,_) <- xts] ++ [pprv t, text boolConName]



instance PPrint RTyVar where
  pprint (RTV α) 
   | ppTyVar ppEnv = ppr_tyvar α
   | otherwise     = ppr_tyvar_short α

ppr_tyvar       = text . tvId
ppr_tyvar_short = tshow

instance (Reftable s, PPrint s, PPrint p, Reftable  p, PPrint t) => PPrint (Ref t s (RType a b c p)) where
  pprint (RMono ss s) = ppRefArgs (fst <$> ss) <+> pprint s
  pprint (RPoly ss s) = ppRefArgs (fst <$> ss) <+> pprint (fromMaybe top (stripRTypeBase s))

ppRefArgs [] = empty
ppRefArgs ss = text "\\" <> hsep (ppRefSym <$> ss ++ [vv Nothing]) <+> text "->"

ppRefSym (S "") = text "_"
ppRefSym s      = pprint s

instance (PPrint r, Reftable r) => PPrint (UReft r) where
  pprint (U r p)
    | isTauto r  = pprint p
    | isTauto p  = pprint r
    | otherwise  = pprint p <> text " & " <> pprint r


