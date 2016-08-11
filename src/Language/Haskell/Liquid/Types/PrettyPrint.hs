-- | This module contains a single function that converts a RType -> Doc
--   without using *any* simplifications.

{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Haskell.Liquid.Types.PrettyPrint
  ( -- * Printable RTypes
    OkRT

    -- * Printers
  , rtypeDoc

  -- * Printing Lists (TODO: move to fixpoint)
  , pprManyOrdered
  , pprintLongList
  , pprintSymbol

  ) where

import qualified Data.HashMap.Strict              as M
import qualified Data.List                        as L                               -- (sort)
import           Data.String
import           ErrUtils                         (ErrMsg)
import           GHC                              (Name, Class)
-- import           Var              (Var)
-- import           TyCon            (TyCon)
-- -- import           Data.Maybe
-- import qualified Data.List    as L -- (sort)
-- import qualified Data.HashMap.Strict as M
-- import           Text.PrettyPrint.HughesPJ
import           HscTypes                         (SourceError)
import           Language.Fixpoint.Misc
import           Language.Fixpoint.Types          hiding (Error, SrcSpan, Predicate)
import           Language.Haskell.Liquid.GHC.Misc
import           Language.Haskell.Liquid.Misc
import           Language.Haskell.Liquid.Types    hiding (sort)
import           Prelude                          hiding (error)
import           SrcLoc
import           Text.PrettyPrint.HughesPJ
import           TyCon                            (TyCon)
import           TypeRep                          hiding (maybeParen)
import           Var                              (Var)

--------------------------------------------------------------------------------
pprManyOrdered :: (PPrint a, Ord a) => Tidy -> String -> [a] -> [Doc]
--------------------------------------------------------------------------------
pprManyOrdered k msg = map ((text msg <+>) . pprintTidy k) . L.sort

--------------------------------------------------------------------------------
pprintLongList :: PPrint a => Tidy -> [a] -> Doc
--------------------------------------------------------------------------------
pprintLongList k = brackets . vcat . map (pprintTidy k)


--------------------------------------------------------------------------------
pprintSymbol :: Symbol -> Doc
--------------------------------------------------------------------------------
pprintSymbol x = char '‘' <> pprint x <> char '’'


--------------------------------------------------------------------------------
-- | A whole bunch of PPrint instances follow ----------------------------------
--------------------------------------------------------------------------------
instance PPrint ErrMsg where
  pprintTidy _ = text . show

instance PPrint SourceError where
  pprintTidy _ = text . show

instance PPrint Var where
  pprintTidy _ = pprDoc

instance PPrint Name where
  pprintTidy _ = pprDoc

instance PPrint TyCon where
  pprintTidy Lossy = shortModules . pprDoc
  pprintTidy Full  =                pprDoc

instance PPrint Type where
  pprintTidy _ = pprDoc -- . tidyType emptyTidyEnv -- WHY WOULD YOU DO THIS???

instance PPrint Class where
  pprintTidy Lossy = shortModules . pprDoc
  pprintTidy Full  =                pprDoc

instance Show Predicate where
  show = showpp

instance (PPrint t) => PPrint (Annot t) where
  pprintTidy k (AnnUse t) = text "AnnUse" <+> pprintTidy k t
  pprintTidy k (AnnDef t) = text "AnnDef" <+> pprintTidy k t
  pprintTidy k (AnnRDf t) = text "AnnRDf" <+> pprintTidy k t
  pprintTidy _ (AnnLoc l) = text "AnnLoc" <+> pprDoc l

instance PPrint a => PPrint (AnnInfo a) where
  pprintTidy k (AI m) = vcat $ pprAnnInfoBinds k <$> M.toList m

instance PPrint a => Show (AnnInfo a) where
  show = showpp

pprAnnInfoBinds :: (PPrint a, PPrint b) => Tidy -> (SrcSpan, [(Maybe a, b)]) -> Doc
pprAnnInfoBinds k (l, xvs)
  = vcat $ (pprAnnInfoBind k . (l,)) <$> xvs

pprAnnInfoBind :: (PPrint a, PPrint b) => Tidy -> (SrcSpan, (Maybe a, b)) -> Doc
pprAnnInfoBind k (RealSrcSpan sp, xv)
  = xd $$ pprDoc l $$ pprDoc c $$ pprintTidy k n $$ vd $$ text "\n\n\n"
    where
      l        = srcSpanStartLine sp
      c        = srcSpanStartCol sp
      (xd, vd) = pprXOT k xv
      n        = length $ lines $ render vd

pprAnnInfoBind _ (_, _)
  = empty

pprXOT :: (PPrint a, PPrint a1) => Tidy -> (Maybe a, a1) -> (Doc, Doc)
pprXOT k (x, v) = (xd, pprintTidy k v)
  where
    xd          = maybe "unknown" (pprintTidy k) x

--------------------------------------------------------------------------------
-- | Pretty Printing RefType ---------------------------------------------------
--------------------------------------------------------------------------------


instance (OkRT c tv r) => PPrint (RType c tv r) where
  -- RJ: THIS IS THE CRUCIAL LINE, the following prints short types.
  pprintTidy _ = rtypeDoc Lossy
  -- pprintTidy _ = ppRType TopPrec

--------------------------------------------------------------------------------
rtypeDoc :: (OkRT c tv r) => Tidy -> RType c tv r -> Doc
--------------------------------------------------------------------------------
rtypeDoc k    = ppr_rtype (ppE k) TopPrec
  where
    ppE Lossy = ppEnvShort ppEnv
    ppE Full  = ppEnv

instance PPrint Tidy where
  pprintTidy _ Full  = "Full"
  pprintTidy _ Lossy = "Lossy"

--------------------------------------------------------------------------------
ppr_rtype :: (OkRT c tv r) => PPEnv -> Prec -> RType c tv r -> Doc
--------------------------------------------------------------------------------
ppr_rtype bb p t@(RAllT _ _)
  = ppr_forall bb p t
ppr_rtype bb p t@(RAllP _ _)
  = ppr_forall bb p t
ppr_rtype bb p t@(RAllS _ _)
  = ppr_forall bb p t
ppr_rtype _ _ (RVar a r)
  = ppTy r $ pprint a
ppr_rtype bb p t@(RFun _ _ _ _)
  = maybeParen p FunPrec $ ppr_rty_fun bb empty t
ppr_rtype bb p (RApp c [t] rs r)
  | isList c
  = ppTy r $ brackets (ppr_rtype bb p t) <> ppReftPs bb p rs
ppr_rtype bb p (RApp c ts rs r)
  | isTuple c
  = ppTy r $ parens (intersperse comma (ppr_rtype bb p <$> ts)) <> ppReftPs bb p rs
ppr_rtype bb p (RApp c ts rs r)
  | isEmpty rsDoc && isEmpty tsDoc
  = ppTy r $ ppT c
  | otherwise
  = ppTy r $ parens $ ppT c <+> rsDoc <+> tsDoc
  where
    rsDoc            = ppReftPs bb p rs
    tsDoc            = hsep (ppr_rtype bb p <$> ts)
    ppT              = ppTyConB bb

ppr_rtype bb p t@(REx _ _ _)
  = ppExists bb p t
ppr_rtype bb p t@(RAllE _ _ _)
  = ppAllExpr bb p t
ppr_rtype _ _ (RExprArg e)
  = braces $ pprint e
ppr_rtype bb p (RAppTy t t' r)
  = ppTy r $ ppr_rtype bb p t <+> ppr_rtype bb p t'
ppr_rtype bb p (RRTy e _ OCons t)
  = sep [braces (ppr_rsubtype bb p e) <+> "=>", ppr_rtype bb p t]
ppr_rtype bb p (RRTy e r o t)
  = sep [ppp (pprint o <+> ppe <+> pprint r), ppr_rtype bb p t]
  where
    ppe  = (hsep $ punctuate comma (ppxt <$> e)) <+> dcolon
    ppp  = \doc -> text "<<" <+> doc <+> text ">>"
    ppxt = \(x, t) -> pprint x <+> ":" <+> ppr_rtype bb p t
ppr_rtype _ _ (RHole r)
  = ppTy r $ text "_"

ppTyConB :: TyConable c => PPEnv -> c -> Doc
ppTyConB bb
  | ppShort bb = shortModules . ppTycon
  | otherwise  = ppTycon

shortModules :: Doc -> Doc
shortModules = text . symbolString . dropModuleNames . symbol . render

ppr_rsubtype
  :: (OkRT c tv r, PPrint a, PPrint (RType c tv r), PPrint (RType c tv ()))
  => PPEnv -> Prec -> [(a, RType c tv r)] -> Doc
ppr_rsubtype bb p e
  = pprint_env <+> text "|-" <+> ppr_rtype bb p tl <+> "<:" <+> ppr_rtype bb p tr
  where
    (el, r)  = (init e,  last e)
    (env, l) = (init el, last el)
    tr   = snd $ r
    tl   = snd $ l
    pprint_bind (x, t) = pprint x <+> colon <> colon <+> ppr_rtype bb p t
    pprint_env         = hsep $ punctuate comma (pprint_bind <$> env)

{- NUKE?
ppSpine (RAllT _ t)      = text "RAllT" <+> parens (ppSpine t)
ppSpine (RAllP _ t)      = text "RAllP" <+> parens (ppSpine t)
ppSpine (RAllS _ t)      = text "RAllS" <+> parens (ppSpine t)
ppSpine (RAllE _ _ t)    = text "RAllE" <+> parens (ppSpine t)
ppSpine (REx _ _ t)      = text "REx" <+> parens (ppSpine t)
ppSpine (RFun _ i o _)   = ppSpine i <+> text "->" <+> ppSpine o
ppSpine (RAppTy t t' _)  = text "RAppTy" <+> parens (ppSpine t) <+> parens (ppSpine t')
ppSpine (RHole _)        = text "RHole"
ppSpine (RApp c _ _ _)   = text "RApp" <+> parens (pprint c)
ppSpine (RVar _ _)       = text "RVar"
ppSpine (RExprArg _)     = text "RExprArg"
ppSpine (RRTy _ _ _ _)   = text "RRTy"

-}

-- | From GHC: TypeRep
maybeParen :: Prec -> Prec -> Doc -> Doc
maybeParen ctxt_prec inner_prec pretty
  | ctxt_prec < inner_prec = pretty
  | otherwise                  = parens pretty

ppExists
  :: (OkRT c tv r, PPrint c, PPrint tv, PPrint (RType c tv r),
      PPrint (RType c tv ()), Reftable (RTProp c tv r),
      Reftable (RTProp c tv ()))
  => PPEnv -> Prec -> RType c tv r -> Doc
ppExists bb p t
  = text "exists" <+> brackets (intersperse comma [ppr_dbind bb TopPrec x t | (x, t) <- zs]) <> dot <> ppr_rtype bb p t'
    where (zs,  t')               = split [] t
          split zs (REx x t t')   = split ((x,t):zs) t'
          split zs t                = (reverse zs, t)

ppAllExpr
  :: (OkRT c tv r, PPrint (RType c tv r), PPrint (RType c tv ()))
  => PPEnv -> Prec -> RType c tv r -> Doc
ppAllExpr bb p t
  = text "forall" <+> brackets (intersperse comma [ppr_dbind bb TopPrec x t | (x, t) <- zs]) <> dot <> ppr_rtype bb p t'
    where (zs,  t')               = split [] t
          split zs (RAllE x t t') = split ((x,t):zs) t'
          split zs t                = (reverse zs, t)

ppReftPs
  :: (OkRT c tv r, PPrint (RType c tv r), PPrint (RType c tv ()),
      Reftable (Ref (RType c tv ()) (RType c tv r)))
  => t -> t1 -> [Ref (RType c tv ()) (RType c tv r)] -> Doc
ppReftPs _ _ rs
  | all isTauto rs   = empty
  | not (ppPs ppEnv) = empty
  | otherwise        = angleBrackets $ hsep $ punctuate comma $ ppr_ref <$> rs

ppr_dbind
  :: (OkRT c tv r, PPrint (RType c tv r), PPrint (RType c tv ()))
  => PPEnv -> Prec -> Symbol -> RType c tv r -> Doc
ppr_dbind bb p x t
  | isNonSymbol x || (x == dummySymbol)
  = ppr_rtype bb p t
  | otherwise
  = pprint x <> colon <> ppr_rtype bb p t


ppr_rty_fun
  :: ( OkRT c tv r, PPrint (RType c tv r), PPrint (RType c tv ()))
  => PPEnv -> Doc -> RType c tv r -> Doc
ppr_rty_fun bb prefix t
  = prefix <+> ppr_rty_fun' bb t

ppr_rty_fun'
  :: ( OkRT c tv r, PPrint (RType c tv r), PPrint (RType c tv ()))
  => PPEnv -> RType c tv r -> Doc
ppr_rty_fun' bb (RFun b t t' r)
  = ppTy r $ ppr_dbind bb FunPrec b t <+> ppr_rty_fun bb arrow t'
ppr_rty_fun' bb t
  = ppr_rtype bb TopPrec t

ppr_forall :: (OkRT c tv r) => PPEnv -> Prec -> RType c tv r -> Doc
ppr_forall bb p t = maybeParen p FunPrec $ sep [
                      ppr_foralls (ppPs bb) (ty_vars trep) (ty_preds trep) (ty_labels trep)
                    , ppr_clss cls
                    , ppr_rtype bb TopPrec t'
                    ]
  where
    trep          = toRTypeRep t
    (cls, t')     = bkClass $ fromRTypeRep $ trep {ty_vars = [], ty_preds = [], ty_labels = []}

    ppr_foralls False _ _  _  = empty
    ppr_foralls _    [] [] [] = empty
    ppr_foralls True αs πs ss = text "forall" <+> dαs αs <+> dπs (ppPs bb) πs <+> ppr_symbols ss <> dot

    ppr_clss []               = empty
    ppr_clss cs               = (parens $ hsep $ punctuate comma (uncurry (ppr_cls bb p) <$> cs)) <+> text "=>"

    dαs αs                    = ppr_rtvar_def αs

    -- dπs :: Bool -> [PVar a] -> Doc
    dπs _ []                  = empty
    dπs False _               = empty
    dπs True πs               = angleBrackets $ intersperse comma $ ppr_pvar_def bb p <$> πs

ppr_rtvar_def :: (PPrint tv) => [RTVar tv (RType c tv ())] -> Doc 
ppr_rtvar_def = sep . map (pprint . ty_var_value)

ppr_symbols :: [Symbol] -> Doc
ppr_symbols [] = empty
ppr_symbols ss = angleBrackets $ intersperse comma $ pprint <$> ss

ppr_cls
  :: (OkRT c tv r, PPrint a, PPrint (RType c tv r),
      PPrint (RType c tv ()))
  => PPEnv -> Prec -> a -> [RType c tv r] -> Doc
ppr_cls bb p c ts
  = pp c <+> hsep (map (ppr_rtype bb p) ts)
  where
    pp | ppShort bb = text . symbolString . dropModuleNames . symbol . render . pprint
       | otherwise  = pprint


ppr_pvar_def :: (OkRT c tv ()) => PPEnv -> Prec -> PVar (RType c tv ()) -> Doc
ppr_pvar_def bb p (PV s t _ xts)
  = pprint s <+> dcolon <+> intersperse arrow dargs <+> ppr_pvar_kind bb p t
  where
    dargs = [ppr_pvar_sort bb p xt | (xt,_,_) <- xts]


ppr_pvar_kind :: (OkRT c tv ()) => PPEnv -> Prec -> PVKind (RType c tv ()) -> Doc
ppr_pvar_kind bb p (PVProp t) = ppr_pvar_sort bb p t <+> arrow <+> ppr_name propConName
ppr_pvar_kind _ _ (PVHProp)   = ppr_name hpropConName

ppr_name :: Symbol -> Doc
ppr_name                      = text . symbolString

ppr_pvar_sort :: (OkRT c tv ()) => PPEnv -> Prec -> RType c tv () -> Doc
ppr_pvar_sort bb p t = ppr_rtype bb p t

ppr_ref :: (OkRT c tv r) => Ref (RType c tv ()) (RType c tv r) -> Doc
ppr_ref  (RProp ss s) = ppRefArgs (fst <$> ss) <+> pprint s
-- ppr_ref (RProp ss s) = ppRefArgs (fst <$> ss) <+> pprint (fromMaybe mempty (stripRTypeBase s))

ppRefArgs :: [Symbol] -> Doc
ppRefArgs [] = empty
ppRefArgs ss = text "\\" <> hsep (ppRefSym <$> ss ++ [vv Nothing]) <+> text "->"

ppRefSym :: (Eq a, IsString a, PPrint a) => a -> Doc
ppRefSym "" = text "_"
ppRefSym s  = pprint s

dot :: Doc
dot                = char '.'

instance (PPrint r, Reftable r) => PPrint (UReft r) where
  pprintTidy k (MkUReft r p _)
    | isTauto r  = pprintTidy k p
    | isTauto p  = pprintTidy k r
    | otherwise  = pprintTidy k p <> text " & " <> pprintTidy k r

--------------------------------------------------------------------------------
