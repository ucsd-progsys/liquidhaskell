-- | This module contains a single function that converts a RType -> Doc
--   without using *any* simplifications.

{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MonoLocalBinds       #-}

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
import           HscTypes                         (SourceError)
import           Language.Fixpoint.Misc
import qualified Language.Fixpoint.Types          as F -- hiding (Error, SrcSpan, Predicate)
import           Language.Haskell.Liquid.GHC.Misc
import           Language.Haskell.Liquid.Misc
import           Language.Haskell.Liquid.Types    hiding (sort)
import           Prelude                          hiding (error)
import           SrcLoc
import           Text.PrettyPrint.HughesPJ
import           TyCon                            (TyCon)
import           Language.Haskell.Liquid.GHC.TypeRep                          hiding (maybeParen)
import           Var                              (Var)

--------------------------------------------------------------------------------
pprManyOrdered :: (PPrint a, Ord a) => F.Tidy -> String -> [a] -> [Doc]
--------------------------------------------------------------------------------
pprManyOrdered k msg = map ((text msg <+>) . pprintTidy k) . L.sort

--------------------------------------------------------------------------------
pprintLongList :: PPrint a => F.Tidy -> [a] -> Doc
--------------------------------------------------------------------------------
pprintLongList k = brackets . vcat . map (pprintTidy k)


--------------------------------------------------------------------------------
pprintSymbol :: F.Symbol -> Doc
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
  pprintTidy F.Lossy = shortModules . pprDoc
  pprintTidy F.Full  =                pprDoc

instance PPrint Type where
  pprintTidy _ = pprDoc -- . tidyType emptyTidyEnv -- WHY WOULD YOU DO THIS???

instance PPrint Class where
  pprintTidy F.Lossy = shortModules . pprDoc
  pprintTidy F.Full  =                pprDoc

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

pprAnnInfoBinds :: (PPrint a, PPrint b) => F.Tidy -> (SrcSpan, [(Maybe a, b)]) -> Doc
pprAnnInfoBinds k (l, xvs)
  = vcat $ (pprAnnInfoBind k . (l,)) <$> xvs

pprAnnInfoBind :: (PPrint a, PPrint b) => F.Tidy -> (SrcSpan, (Maybe a, b)) -> Doc
pprAnnInfoBind k (RealSrcSpan sp, xv)
  = xd $$ pprDoc l $$ pprDoc c $$ pprintTidy k n $$ vd $$ text "\n\n\n"
    where
      l        = srcSpanStartLine sp
      c        = srcSpanStartCol sp
      (xd, vd) = pprXOT k xv
      n        = length $ lines $ render vd

pprAnnInfoBind _ (_, _)
  = empty

pprXOT :: (PPrint a, PPrint a1) => F.Tidy -> (Maybe a, a1) -> (Doc, Doc)
pprXOT k (x, v) = (xd, pprintTidy k v)
  where
    xd          = maybe "unknown" (pprintTidy k) x

instance PPrint LMap where
  pprintTidy _ (LMap x xs e) = hcat [pprint x, pprint xs, text "|->", pprint e ]

instance PPrint LogicMap where
  pprintTidy _ (LM lm am) = vcat [ text "Logic Map"
                                 , nest 2 $ text "logic-map"
                                 , nest 4 $ pprint lm
                                 , nest 2 $ text "axiom-map"
                                 , nest 4 $ pprint am
                                 ]
--------------------------------------------------------------------------------
-- | Pretty Printing RefType ---------------------------------------------------
--------------------------------------------------------------------------------
instance (OkRT c tv r) => PPrint (RType c tv r) where
  -- RJ: THIS IS THE CRUCIAL LINE, the following prints short types.
  pprintTidy _ = rtypeDoc F.Lossy
  -- pprintTidy _ = ppRType TopPrec

instance (PPrint tv, PPrint ty) => PPrint (RTAlias tv ty) where
  pprintTidy = ppAlias

ppAlias :: (PPrint tv, PPrint ty) => F.Tidy -> RTAlias tv ty -> Doc
ppAlias k a = text "type" <+> pprint (rtName a)
                          <+> pprints k space (rtTArgs a)
                          <+> pprints k space (rtVArgs a)
                          <+> text " = "
                          <+> pprint (rtBody a)

pprints :: (PPrint a) => F.Tidy -> Doc -> [a] -> Doc
pprints k c = sep . punctuate c . map (pprintTidy k)

--------------------------------------------------------------------------------
rtypeDoc :: (OkRT c tv r) => F.Tidy -> RType c tv r -> Doc
--------------------------------------------------------------------------------
rtypeDoc k    = ppr_rtype (ppE k) TopPrec
  where
    ppE F.Lossy = ppEnvShort ppEnv
    ppE F.Full  = ppEnv

instance PPrint F.Tidy where
  pprintTidy _ F.Full  = "Full"
  pprintTidy _ F.Lossy = "Lossy"

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
  = F.ppTy r $ pprint a
ppr_rtype bb p t@(RFun _ _ _ _)
  = maybeParen p FunPrec $ ppr_rty_fun bb empty t
ppr_rtype bb p (RApp c [t] rs r)
  | isList c
  = F.ppTy r $ brackets (ppr_rtype bb p t) <> ppReftPs bb p rs
ppr_rtype bb p (RApp c ts rs r)
  | isTuple c
  = F.ppTy r $ parens (intersperse comma (ppr_rtype bb p <$> ts)) <> ppReftPs bb p rs
ppr_rtype bb p (RApp c ts rs r)
  | isEmpty rsDoc && isEmpty tsDoc
  = F.ppTy r $ ppT c
  | otherwise
  = F.ppTy r $ parens $ ppT c <+> rsDoc <+> tsDoc
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
  = F.ppTy r $ ppr_rtype bb p t <+> ppr_rtype bb p t'
ppr_rtype bb p (RRTy e _ OCons t)
  = sep [braces (ppr_rsubtype bb p e) <+> "=>", ppr_rtype bb p t]
ppr_rtype bb p (RRTy e r o t)
  = sep [ppp (pprint o <+> ppe <+> pprint r), ppr_rtype bb p t]
  where
    ppe  = (hsep $ punctuate comma (ppxt <$> e)) <+> dcolon
    ppp  = \doc -> text "<<" <+> doc <+> text ">>"
    ppxt = \(x, t) -> pprint x <+> ":" <+> ppr_rtype bb p t
ppr_rtype _ _ (RHole r)
  = F.ppTy r $ text "_"

ppTyConB :: TyConable c => PPEnv -> c -> Doc
ppTyConB bb
  | ppShort bb = shortModules . ppTycon
  | otherwise  = ppTycon

shortModules :: Doc -> Doc
shortModules = text . F.symbolString . dropModuleNames . F.symbol . render

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

-- | From GHC: TypeRep
maybeParen :: Prec -> Prec -> Doc -> Doc
maybeParen ctxt_prec inner_prec pretty
  | ctxt_prec < inner_prec = pretty
  | otherwise                  = parens pretty

ppExists
  :: (OkRT c tv r, PPrint c, PPrint tv, PPrint (RType c tv r),
      PPrint (RType c tv ()), F.Reftable (RTProp c tv r),
      F.Reftable (RTProp c tv ()))
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
      F.Reftable (Ref (RType c tv ()) (RType c tv r)))
  => t -> t1 -> [Ref (RType c tv ()) (RType c tv r)] -> Doc
ppReftPs _ _ rs
  | all F.isTauto rs   = empty
  | not (ppPs ppEnv) = empty
  | otherwise        = angleBrackets $ hsep $ punctuate comma $ ppr_ref <$> rs

ppr_dbind
  :: (OkRT c tv r, PPrint (RType c tv r), PPrint (RType c tv ()))
  => PPEnv -> Prec -> F.Symbol -> RType c tv r -> Doc
ppr_dbind bb p x t
  | F.isNonSymbol x || (x == F.dummySymbol)
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
  = F.ppTy r $ ppr_dbind bb FunPrec b t <+> ppr_rty_fun bb arrow t'
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

ppr_symbols :: [F.Symbol] -> Doc
ppr_symbols [] = empty
ppr_symbols ss = angleBrackets $ intersperse comma $ pprint <$> ss

ppr_cls
  :: (OkRT c tv r, PPrint a, PPrint (RType c tv r),
      PPrint (RType c tv ()))
  => PPEnv -> Prec -> a -> [RType c tv r] -> Doc
ppr_cls bb p c ts
  = pp c <+> hsep (map (ppr_rtype bb p) ts)
  where
    pp | ppShort bb = text . F.symbolString . dropModuleNames . F.symbol . render . pprint
       | otherwise  = pprint


ppr_pvar_def :: (OkRT c tv ()) => PPEnv -> Prec -> PVar (RType c tv ()) -> Doc
ppr_pvar_def bb p (PV s t _ xts)
  = pprint s <+> dcolon <+> intersperse arrow dargs <+> ppr_pvar_kind bb p t
  where
    dargs = [ppr_pvar_sort bb p xt | (xt,_,_) <- xts]


ppr_pvar_kind :: (OkRT c tv ()) => PPEnv -> Prec -> PVKind (RType c tv ()) -> Doc
ppr_pvar_kind bb p (PVProp t) = ppr_pvar_sort bb p t <+> arrow <+> ppr_name F.boolConName -- propConName
ppr_pvar_kind _ _ (PVHProp)   = panic Nothing "TODO: ppr_pvar_kind:hprop" -- ppr_name hpropConName

ppr_name :: F.Symbol -> Doc
ppr_name                      = text . F.symbolString

ppr_pvar_sort :: (OkRT c tv ()) => PPEnv -> Prec -> RType c tv () -> Doc
ppr_pvar_sort bb p t = ppr_rtype bb p t

ppr_ref :: (OkRT c tv r) => Ref (RType c tv ()) (RType c tv r) -> Doc
ppr_ref  (RProp ss s) = ppRefArgs (fst <$> ss) <+> pprint s
-- ppr_ref (RProp ss s) = ppRefArgs (fst <$> ss) <+> pprint (fromMaybe mempty (stripRTypeBase s))

ppRefArgs :: [F.Symbol] -> Doc
ppRefArgs [] = empty
ppRefArgs ss = text "\\" <> hsep (ppRefSym <$> ss ++ [F.vv Nothing]) <+> text "->"

ppRefSym :: (Eq a, IsString a, PPrint a) => a -> Doc
ppRefSym "" = text "_"
ppRefSym s  = pprint s

dot :: Doc
dot                = char '.'

instance (PPrint r, F.Reftable r) => PPrint (UReft r) where
  pprintTidy k (MkUReft r p _)
    | F.isTauto r  = pprintTidy k p
    | F.isTauto p  = pprintTidy k r
    | otherwise  = pprintTidy k p <> text " & " <> pprintTidy k r

--------------------------------------------------------------------------------
