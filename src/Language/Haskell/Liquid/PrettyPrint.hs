{-# LANGUAGE FlexibleContexts           #-} 
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE UndecidableInstances       #-}
-- | Module with all the printing routines

module Language.Haskell.Liquid.PrettyPrint (
  
  -- * Printing RType
    ppr_rtype

  -- * Converting To String
  , showpp

  -- * Printing an Orderable List
  , pprManyOrdered 
  -- * Printing a List with many large items
  , pprintLongList
  , ppSpine
  ) where

import ErrUtils                         (ErrMsg)
import HscTypes                         (SourceError)
import SrcLoc                           (SrcSpan)
import GHC                              (Name)
import TcType                           (tidyType)
import VarEnv                           (emptyTidyEnv)
import Language.Haskell.Liquid.GhcMisc
import Text.PrettyPrint.HughesPJ
import Language.Fixpoint.Types hiding (Predicate)
import Language.Fixpoint.Misc
import Language.Haskell.Liquid.Types hiding (sort)
import Language.Fixpoint.Names (dropModuleNames, symSepName, funConName, listConName, tupConName, propConName, boolConName)
import TypeRep          hiding (maybeParen, pprArrowChain)  
import Text.Parsec.Pos  (SourcePos)
import Text.Parsec.Error (ParseError)
import Var              (Var)
import Control.Applicative ((<$>))
import Data.Maybe   (fromMaybe)
import Data.List    (sort)
import Data.Function (on)
import Data.Monoid   (mempty)

instance PPrint ErrMsg where
  pprint = text . show

instance PPrint SourceError where
  pprint = text . show

instance PPrint ParseError where 
  pprint = text . show 

instance PPrint Var where
  pprint = pprDoc 

instance PPrint Name where
  pprint = pprDoc 

instance PPrint Type where
  pprint = pprDoc . tidyType emptyTidyEnv

instance Show Predicate where
  show = showpp



-- | Printing an Ordered List

---------------------------------------------------------------
pprManyOrdered :: (PPrint a, Ord a) => String -> [a] -> [Doc]
---------------------------------------------------------------
pprManyOrdered msg = map ((text msg <+>) . pprint) . sort -- By (compare `on` pos) 


---------------------------------------------------------------
-- | Pretty Printing RefType ----------------------------------
---------------------------------------------------------------

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
ppr_rtype bb p (RRTy r t)         
  = text "<<" <+> pprint r <+> text ">>" <+> ppr_rtype bb p t
ppr_rtype _ _ (RHole r)
  = ppTy r $ text "_"

ppSpine (RAllT _ t)      = text "RAllT" <+> parens (ppSpine t)
ppSpine (RAllP _ t)      = text "RAllP" <+> parens (ppSpine t)
ppSpine (RAllE _ _ t)    = text "RAllE" <+> parens (ppSpine t)
ppSpine (REx _ _ t)      = text "REx" <+> parens (ppSpine t)
ppSpine (RFun _ i o _)   = ppSpine i <+> text "->" <+> ppSpine o
ppSpine (RAppTy t t' _)  = text "RAppTy" <+> parens (ppSpine t) <+> parens (ppSpine t')
ppSpine (RHole r)        = text "RHole"
ppSpine (RCls c ts)      = text "RCls" <+> parens (ppCls c ts)
ppSpine (RApp c ts rs _) = text "RApp" <+> parens (pprint c)
ppSpine (RVar v _)       = text "RVar"
ppSpine (RExprArg _)     = text "RExprArg"
ppSpine (ROth s)         = text "ROth" <+> text s
ppSpine (RRTy _ _)       = text "RRTy"

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
ppr_tyvar_short = text . showPpr

instance (Reftable s, PPrint s, PPrint p, Reftable  p, PPrint t, PPrint (RType a b c p)) => PPrint (Ref t s (RType a b c p)) where
  pprint (RMono ss s) = ppRefArgs (fst <$> ss) <+> pprint s
  pprint (RPoly ss s) = ppRefArgs (fst <$> ss) <+> pprint (fromMaybe mempty (stripRTypeBase s))

ppRefArgs [] = empty
ppRefArgs ss = text "\\" <> hsep (ppRefSym <$> ss ++ [vv Nothing]) <+> text "->"

ppRefSym (S "") = text "_"
ppRefSym s      = pprint s

instance (PPrint r, Reftable r) => PPrint (UReft r) where
  pprint (U r p)
    | isTauto r  = pprint p
    | isTauto p  = pprint r
    | otherwise  = pprint p <> text " & " <> pprint r

pprintLongList :: PPrint a => [a] -> Doc
pprintLongList = brackets . vcat . map pprint
