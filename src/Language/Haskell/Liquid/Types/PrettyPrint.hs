-- | This module contains a single function that converts a RType -> Doc
--   without using *any* simplifications.

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE TupleSections     #-}

module Language.Haskell.Liquid.Types.PrettyPrint
  ( -- * Printable RTypes
    OkRT
    -- * Printers
  , rtypeDoc
  , pprRType

  -- * Printing Lists (TODO: move to fixpoint)
  , pprManyOrdered
  , pprintLongList
  , pprintSymbol

  ) where

import           Prelude hiding (error)
import           TypeRep hiding (maybeParen)
import           ErrUtils                         (ErrMsg)
import           HscTypes                         (SourceError)
import           SrcLoc
import           GHC                              (Name, Class)
import           Var              (Var)
import           TyCon            (TyCon)
import           Data.Maybe
import qualified Data.List    as L -- (sort)
import qualified Data.HashMap.Strict as M
import           Text.PrettyPrint.HughesPJ
import           Language.Fixpoint.Misc
import           Language.Haskell.Liquid.Misc
import           Language.Haskell.Liquid.GHC.Misc
import           Language.Fixpoint.Types       hiding (Error, SrcSpan, Predicate)
import           Language.Haskell.Liquid.Types hiding (sort)

--------------------------------------------------------------------------------
pprManyOrdered :: (PPrint a, Ord a) => Tidy -> String -> [a] -> [Doc]
--------------------------------------------------------------------------------
pprManyOrdered k msg = map ((text msg <+>) . pprintTidy k) . L.sort

--------------------------------------------------------------------------------
pprintLongList :: PPrint a => [a] -> Doc
--------------------------------------------------------------------------------
pprintLongList = brackets . vcat . map pprint


--------------------------------------------------------------------------------
pprintSymbol :: Symbol -> Doc
--------------------------------------------------------------------------------
pprintSymbol x = char '‘' <> pprint x <> char '’'


--------------------------------------------------------------------------------
-- | A whole bunch of PPrint instances follow ----------------------------------
--------------------------------------------------------------------------------
instance PPrint ErrMsg where
  pprint = text . show

instance PPrint SourceError where
  pprint = text . show

instance PPrint Var where
  pprint = pprDoc

instance PPrint Name where
  pprint = pprDoc

instance PPrint TyCon where
  pprint = pprDoc

instance PPrint Type where
  pprint = pprDoc -- . tidyType emptyTidyEnv -- WHY WOULD YOU DO THIS???

instance PPrint Class where
  pprint = pprDoc

instance Show Predicate where
  show = showpp

instance (PPrint t) => PPrint (Annot t) where
  pprint (AnnUse t) = text "AnnUse" <+> pprint t
  pprint (AnnDef t) = text "AnnDef" <+> pprint t
  pprint (AnnRDf t) = text "AnnRDf" <+> pprint t
  pprint (AnnLoc l) = text "AnnLoc" <+> pprDoc l

instance PPrint a => PPrint (AnnInfo a) where
  pprint (AI m) = vcat $ map pprAnnInfoBinds $ M.toList m

instance PPrint a => Show (AnnInfo a) where
  show = showpp

pprAnnInfoBinds (l, xvs)
  = vcat $ map (pprAnnInfoBind . (l,)) xvs

pprAnnInfoBind (RealSrcSpan k, xv)
  = xd $$ pprDoc l $$ pprDoc c $$ pprint n $$ vd $$ text "\n\n\n"
    where
      l        = srcSpanStartLine k
      c        = srcSpanStartCol k
      (xd, vd) = pprXOT xv
      n        = length $ lines $ render vd

pprAnnInfoBind (_, _)
  = empty

pprXOT (x, v) = (xd, pprint v)
  where
    xd = maybe (text "unknown") pprint x
--------------------------------------------------------------------------------
-- | Pretty Printing RefType ---------------------------------------------------
--------------------------------------------------------------------------------

-- Should just make this a @Pretty@ instance but its too damn tedious
-- to figure out all the constraints.

type OkRT c tv r = ( TyConable c
                   , PPrint tv
                   , PPrint c
                   , PPrint r
                   , Reftable r
                   , Reftable (RTProp c tv ())
                   , Reftable (RTProp c tv r)
                   , RefTypable c tv ()
                   , RefTypable c tv r
                   )

--------------------------------------------------------------------------------
rtypeDoc :: (OkRT c tv r) => Tidy -> RType c tv r -> Doc
--------------------------------------------------------------------------------
rtypeDoc k    = pprRType (ppE k) TopPrec
  where
    ppE Lossy = ppEnvShort ppEnv
    ppE Full  = ppEnv

--------------------------------------------------------------------------------
pprRType :: (OkRT c tv r) => PPEnv -> Prec -> RType c tv r -> Doc
--------------------------------------------------------------------------------
pprRType bb p t@(RAllT _ _)
  = ppr_forall bb p t
pprRType bb p t@(RAllP _ _)
  = ppr_forall bb p t
pprRType bb p t@(RAllS _ _)
  = ppr_forall bb p t
pprRType _ _ (RVar a r)
  = ppTy r $ pprint a
pprRType bb p t@(RFun {})
  = maybeParen p FunPrec $ pprRtyFun bb empty t
pprRType bb p (RApp c [t] rs r)
  | isList c
  = ppTy r $ brackets (pprRType bb p t) <> ppReftPs bb p rs
pprRType bb p (RApp c ts rs r)
  | isTuple c
  = ppTy r $ parens (intersperse comma (pprRType bb p <$> ts)) <> ppReftPs bb p rs
pprRType bb p (RApp c ts rs r)
  | isEmpty rsDoc && isEmpty tsDoc
  = ppTy r $ ppT c
  | otherwise
  = ppTy r $ parens $ ppT c <+> rsDoc <+> tsDoc
  where
    rsDoc            = ppReftPs bb p rs
    tsDoc            = hsep (pprRType bb p <$> ts)
    ppT              = ppTyConB bb

pprRType bb p t@(REx {})
  = ppExists bb p t
pprRType bb p t@(RAllE {})
  = ppAllExpr bb p t
pprRType _ _ (RExprArg e)
  = braces $ pprint e
pprRType bb p (RAppTy t t' r)
  = ppTy r $ pprRType bb p t <+> pprRType bb p t'
pprRType bb p (RRTy e _ OCons t)
  = sep [braces (pprRSubType bb p e) <+> "=>", pprRType bb p t]
pprRType bb p (RRTy e r o t)
  = sep [ppp (pprint o <+> ppe <+> pprint r), pprRType bb p t]
  where
    ppe         = hsep (punctuate comma (ppxt <$> e)) <+> dcolon
    ppp d       = "<<" <+> d <+> ">>"
    ppxt (x, t) = pprint x <+> ":" <+> pprRType bb p t
pprRType _ _ (RHole r)
  = ppTy r "_"

ppTyConB bb
  | ppShort bb = text . symbolString . dropModuleNames . symbol . render . ppTycon
  | otherwise  = ppTycon

pprRSubType bb p e
  = ppEnv <+> text "|-" <+> pprRType bb p tl <+> "<:" <+> pprRType bb p tr
  where
    (el, r)       = (init e,  last e)
    (env, l)      = (init el, last el)
    tr            = snd r
    tl            = snd l
    ppBind (x, t) = pprint x <+> colon <> colon <+> pprRType bb p t
    ppEnv         = hsep $ punctuate comma (ppBind <$> env)

-- | From GHC: TypeRep
maybeParen :: Prec -> Prec -> Doc -> Doc
maybeParen ctxt_prec inner_prec pretty
  | ctxt_prec < inner_prec = pretty
  | otherwise                  = parens pretty

-- ppExists :: (RefTypable p c tv (), RefTypable p c tv r) => Bool -> Prec -> RType p c tv r -> Doc
ppExists bb p t
  = text "exists" <+> brackets (intersperse comma [pprDbind bb TopPrec x t | (x, t) <- zs]) <> dot <> pprRType bb p t'
    where (zs,  t')               = split [] t
          split zs (REx x t t')   = split ((x,t):zs) t'
          split zs t                = (reverse zs, t)

-- ppAllExpr :: (RefTypable p c tv (), RefTypable p c tv r) => Bool -> Prec -> RType p c tv r -> Doc
ppAllExpr bb p t
  = text "forall" <+> brackets (intersperse comma [pprDbind bb TopPrec x t | (x, t) <- zs]) <> dot <> pprRType bb p t'
    where (zs,  t')               = split [] t
          split zs (RAllE x t t') = split ((x,t):zs) t'
          split zs t                = (reverse zs, t)

ppReftPs _ _ rs
  | all isTauto rs   = empty
  -- RJ FIXHOLE | not (ppPs ppEnv) = empty
  | otherwise        = angleBrackets $ hsep $ punctuate comma $ pprRef <$> rs

-- pprDbind :: (RefTypable p c tv (), RefTypable p c tv r) => Bool -> Prec -> Symbol -> RType p c tv r -> Doc
pprDbind bb p x t
  | isNonSymbol x || (x == dummySymbol)
  = pprRType bb p t
  | otherwise
  = pprint x <> colon <> pprRType bb p t


pprRtyFun bb prefix t
  = prefix <+> pprRtyFun' bb t

pprRtyFun' bb (RFun b t t' _)
  = pprDbind bb FunPrec b t <+> pprRtyFun bb arrow t'
pprRtyFun' bb t
  = pprRType bb TopPrec t


-- ppr_forall :: (RefTypable p c tv (), RefTypable p c tv r) => Bool -> Prec -> RType p c tv r -> Doc
ppr_forall :: (OkRT c tv r) => PPEnv -> Prec -> RType c tv r -> Doc
ppr_forall bb p t = maybeParen p FunPrec $ sep [
                      ppr_foralls (ppPs bb) (ty_vars trep) (ty_preds trep) (ty_labels trep)
                    , ppr_clss cls
                    , pprRType bb TopPrec t'
                    ]
  where
    trep          = toRTypeRep t
    (cls, t')     = bkClass $ fromRTypeRep $ trep {ty_vars = [], ty_preds = [], ty_labels = []}

    ppr_foralls False _ _  _  = empty
    ppr_foralls _    [] [] [] = empty
    ppr_foralls True αs πs ss = text "forall" <+> dαs αs <+> dπs (ppPs bb) πs <+> pprSymbols ss <> dot

    ppr_clss []               = empty
    ppr_clss cs               = parens (hsep $ punctuate comma (uncurry (ppr_cls bb p) <$> cs)) <+> text "=>"

    dαs αs                    = sep $ pprint <$> αs

    -- dπs :: Bool -> [PVar a] -> Doc
    dπs _ []                  = empty
    dπs False _               = empty
    dπs True πs               = angleBrackets $ intersperse comma $ pprPvarDef bb p <$> πs

pprSymbols    :: [Symbol] -> Doc
pprSymbols [] = empty
pprSymbols ss = angleBrackets $ intersperse comma $ pprint <$> ss

ppr_cls bb p c ts
  = pp c <+> hsep (map (pprRType bb p) ts)
  where
    pp | ppShort bb = text . symbolString . dropModuleNames . symbol . render . pprint
       | otherwise  = pprint


pprPvarDef :: (OkRT c tv ()) => PPEnv -> Prec -> PVar (RType c tv ()) -> Doc
pprPvarDef bb p (PV s t _ xts)
  = pprint s <+> dcolon <+> intersperse arrow dargs <+> pprPvarKind bb p t
  where
    dargs = [pprPvarSort bb p xt | (xt,_,_) <- xts]


pprPvarKind :: (OkRT c tv ()) => PPEnv -> Prec -> PVKind (RType c tv ()) -> Doc
pprPvarKind bb p (PVProp t) = pprPvarSort bb p t <+> arrow <+> pprName propConName
pprPvarKind _ _ (PVHProp)   = pprName hpropConName
pprName                      = text . symbolString

pprPvarSort :: (OkRT c tv ()) => PPEnv -> Prec -> RType c tv () -> Doc
pprPvarSort bb p t = pprRType bb p t

pprRef :: (OkRT c tv r) => Ref (RType c tv ()) (RType c tv r) -> Doc
pprRef (RProp ss (RHole s)) = ppRefArgs (fst <$> ss) <+> pprint s
pprRef (RProp ss s)         = ppRefArgs (fst <$> ss) <+> pprint (fromMaybe mempty (stripRTypeBase s))

ppRefArgs :: [Symbol] -> Doc
ppRefArgs [] = empty
ppRefArgs ss = text "\\" <> hsep (ppRefSym <$> ss ++ [vv Nothing]) <+> text "->"

ppRefSym "" = text "_"
ppRefSym s  = pprint s

dot                = char '.'

instance (PPrint r, Reftable r) => PPrint (UReft r) where
  pprint (MkUReft r p _)
    | isTauto r  = pprint p
    | isTauto p  = pprint r
    | otherwise  = pprint p <> text " & " <> pprint r

--------------------------------------------------------------------------------
