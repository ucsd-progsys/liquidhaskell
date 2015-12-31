{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TupleSections        #-}

-- | Module with all the printing and serialization routines

module Language.Haskell.Liquid.UX.PrettyPrint (
  -- * Tidy level
  Tidy (..)

  -- * Printing RType
  , rtypeDoc
  , ppr_rtype

  -- * Printing an Orderable List
  , pprManyOrdered

  -- * Printing a List with many large items
  , pprintLongList
  , ppSpine
  , pprintSymbol
  ) where

import ErrUtils                         (ErrMsg)
import HscTypes                         (SourceError)
import SrcLoc
import GHC                              (Name, Class)
import TypeRep          hiding (maybeParen, pprArrowChain)
import Var              (Var)
import TyCon            (TyCon)


import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.GHC.Misc
import Language.Fixpoint.Types hiding (Error, SrcSpan, Predicate)
import Language.Fixpoint.Misc
import Language.Haskell.Liquid.Types hiding (sort)
import Language.Haskell.Liquid.UX.Tidy

import Text.Parsec.Error (ParseError, errorMessages, showErrorMessages)
import Text.PrettyPrint.HughesPJ

import Data.Maybe   (fromMaybe)
import Data.List    (sort, sortBy)
import Data.Function (on)
import Data.Aeson

-- import Data.Monoid   (mempty)
-- import Control.Applicative ((<$>))

import qualified Control.Exception  as Ex
import qualified Data.HashMap.Strict as M


pprintSymbol :: Symbol -> Doc
pprintSymbol x = char '‘' <> pprint x <> char '’'

instance PPrint SrcSpan where
  pprint = pprDoc

-- instance PPrint Doc where
--   pprint x = x

instance PPrint ErrMsg where
  pprint = text . show

instance PPrint SourceError where
  pprint = text . show

instance PPrint ParseError where
  pprint e = vcat $ tail $ map text ls
    where
      ls = lines $ showErrorMessages "or" "unknown parse error"
                                     "expecting" "unexpected" "end of input"
                                     (errorMessages e)

-- instance PPrint LParseError where
--   pprint (LPE _ msgs) = text "Parse Error: " <> vcat (map pprint msgs)

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


-- | Printing an Ordered List

---------------------------------------------------------------
pprManyOrdered :: (PPrint a, Ord a) => Tidy -> String -> [a] -> [Doc]
---------------------------------------------------------------
pprManyOrdered k msg = map ((text msg <+>) . pprintTidy k) . sort


---------------------------------------------------------------
-- | Pretty Printing RefType ----------------------------------
---------------------------------------------------------------

-- Should just make this a @Pretty@ instance but its too damn tedious
-- to figure out all the constraints.

rtypeDoc k    = ppr_rtype (ppE k) TopPrec
  where
    ppE Lossy = ppEnvShort ppEnv
    ppE Full  = ppEnv

ppTyConB bb
  | ppShort bb = text . symbolString . dropModuleNames . symbol . render . ppTycon
  | otherwise  = ppTycon


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
  = ppTy r $ brackets (ppr_rtype bb p t) <> ppReftPs bb rs
ppr_rtype bb p (RApp c ts rs r)
  | isTuple c
  = ppTy r $ parens (intersperse comma (ppr_rtype bb p <$> ts)) <> ppReftPs bb rs
ppr_rtype bb p (RApp c ts rs r)
  | isEmpty rsDoc && isEmpty tsDoc
  = ppTy r $ ppT c
  | otherwise
  = ppTy r $ parens $ ppT c <+> rsDoc <+> tsDoc
  where
    rsDoc            = ppReftPs bb rs
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
  where ppe = (hsep $ punctuate comma (pprint <$> e)) <+> colon <> colon
        ppp = \doc -> text "<<" <+> doc <+> text ">>"
ppr_rtype _ _ (RHole r)
  = ppTy r $ text "_"


ppr_rsubtype bb p e
  = pprint_env <+> text "|-" <+> ppr_rtype bb p tl <+> "<:" <+> ppr_rtype bb p tr
  where
    (el, r)  = (init e,  last e)
    (env, l) = (init el, last el)
    tr   = snd $ r
    tl   = snd $ l
    pprint_bind (x, t) = pprint x <+> colon <> colon <+> ppr_rtype bb p t
    pprint_env         = hsep $ punctuate comma (pprint_bind <$> env)

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

-- | From GHC: TypeRep
maybeParen :: Prec -> Prec -> Doc -> Doc
maybeParen ctxt_prec inner_prec pretty
  | ctxt_prec < inner_prec = pretty
  | otherwise                  = parens pretty


-- ppExists :: (RefTypable p c tv (), RefTypable p c tv r) => Bool -> Prec -> RType p c tv r -> Doc
ppExists bb p t
  = text "exists" <+> brackets (intersperse comma [ppr_dbind bb TopPrec x t | (x, t) <- zs]) <> dot <> ppr_rtype bb p t'
    where (zs,  t')               = split [] t
          split zs (REx x t t')   = split ((x,t):zs) t'
          split zs t                = (reverse zs, t)

-- ppAllExpr :: (RefTypable p c tv (), RefTypable p c tv r) => Bool -> Prec -> RType p c tv r -> Doc
ppAllExpr bb p t
  = text "forall" <+> brackets (intersperse comma [ppr_dbind bb TopPrec x t | (x, t) <- zs]) <> dot <> ppr_rtype bb p t'
    where (zs,  t')               = split [] t
          split zs (RAllE x t t') = split ((x,t):zs) t'
          split zs t                = (reverse zs, t)

ppReftPs _ rs
  | all isTauto rs   = empty
  | not (ppPs ppEnv) = empty
  | otherwise        = angleBrackets $ hsep $ punctuate comma $ pprint <$> rs

-- ppr_dbind :: (RefTypable p c tv (), RefTypable p c tv r) => Bool -> Prec -> Symbol -> RType p c tv r -> Doc
ppr_dbind bb p x t
  | isNonSymbol x || (x == dummySymbol)
  = ppr_rtype bb p t
  | otherwise
  = pprint x <> colon <> ppr_rtype bb p t


ppr_rty_fun bb prefix t
  = prefix <+> ppr_rty_fun' bb t

ppr_rty_fun' bb (RFun b t t' _)
  = ppr_dbind bb FunPrec b t <+> ppr_rty_fun bb arrow t'
ppr_rty_fun' bb t
  = ppr_rtype bb TopPrec t


-- ppr_forall :: (RefTypable p c tv (), RefTypable p c tv r) => Bool -> Prec -> RType p c tv r -> Doc
ppr_forall bb p t
  = maybeParen p FunPrec $ sep [ ppr_foralls (ppPs bb) (ty_vars trep) (ty_preds trep) (ty_labels trep) , ppr_clss cls, ppr_rtype bb TopPrec t' ]
  where
    trep                   = toRTypeRep t
    (cls, t')              = bkClass $ fromRTypeRep $ trep {ty_vars = [], ty_preds = [], ty_labels = []}

    ppr_foralls False _ _  _= empty
    ppr_foralls _    [] [] [] = empty
    ppr_foralls True αs πs ss = text "forall" <+> dαs αs <+> dπs (ppPs bb) πs <+> dss (ppSs bb) ss <> dot
    ppr_clss []            = empty
    ppr_clss cs            = (parens $ hsep $ punctuate comma (uncurry (ppr_cls bb p) <$> cs)) <+> text "=>"

    dαs αs                 = sep $ pprint <$> αs

    dπs _ []               = empty
    dπs False _            = empty
    dπs True πs            = angleBrackets $ intersperse comma $ ppr_pvar_def pprint <$> πs
    dss _ []               = empty
    dss _ ss               = angleBrackets $ intersperse comma $ pprint <$> ss


ppr_cls bb p c ts
  = pp c <+> hsep (map (ppr_rtype bb p) ts)
  where
    pp | ppShort bb = text . symbolString . dropModuleNames . symbol . render . pprint
       | otherwise  = pprint


ppr_pvar_def pprv (PV s t _ xts)
  = pprint s <+> dcolon <+> intersperse arrow dargs <+> ppr_pvar_kind pprv t

  where
    dargs = [pprv t | (t,_,_) <- xts]

ppr_pvar_kind pprv (PVProp t) = pprv t <+> arrow <+> ppr_name propConName
ppr_pvar_kind _    (PVHProp)  = ppr_name hpropConName
ppr_name                      = text . symbolString

instance PPrint RTyVar where
  pprint (RTV α)
   | ppTyVar ppEnv = ppr_tyvar α
   | otherwise     = ppr_tyvar_short α

ppr_tyvar       = text . tvId
ppr_tyvar_short = text . showPpr

instance (PPrint p, Reftable  p, PPrint t, PPrint (RType b c p)) => PPrint (Ref t (RType b c p)) where
  pprint (RProp ss (RHole s)) = ppRefArgs (fst <$> ss) <+> pprint s
  pprint (RProp ss s) = ppRefArgs (fst <$> ss) <+> pprint (fromMaybe mempty (stripRTypeBase s))


ppRefArgs [] = empty
ppRefArgs ss = text "\\" <> hsep (ppRefSym <$> ss ++ [vv Nothing]) <+> text "->"

ppRefSym "" = text "_"
ppRefSym s  = pprint s

instance (PPrint r, Reftable r) => PPrint (UReft r) where
  pprint (MkUReft r p _)
    | isTauto r  = pprint p
    | isTauto p  = pprint r
    | otherwise  = pprint p <> text " & " <> pprint r

pprintLongList :: PPrint a => [a] -> Doc
pprintLongList = brackets . vcat . map pprint

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

{-
   TODO: Not exported/never called. Do I have any reason to exist?

ppTable m = vcat $ pprxt <$> xts
  where
    pprxt (x,t) = pprint x $$ nest n (colon <+> pprint t)
    n          = 1 + maximumWithDefault 0 [ i | (x, _) <- xts, let i = keySize x, i <= thresh ]
    keySize     = length . render . pprint
    xts         = sortBy (compare `on` fst) $ M.toList m
    thresh      = 6

maximumWithDefault zero [] = zero
maximumWithDefault _    xs = maximum xs
-}
dot                = char '.'

--------------------------------------------------------------------------------
-- | Pretty Printing Error Messages --------------------------------------------
--------------------------------------------------------------------------------

-- | Need to put @PPrint Error@ instance here (instead of in Types),
--   as it depends on @PPrint SpecTypes@, which lives in this module.

instance PPrint Error where
  pprint       = pprintTidy Full
  pprintTidy k = ppError k . fmap ppSpecTypeErr

ppSpecTypeErr :: SpecType -> Doc
ppSpecTypeErr = rtypeDoc Lossy
              . tidySpecType Lossy
              . fmap (everywhere (mkT noCasts))
  where
    noCasts (ECst x _) = x
    noCasts e          = e

instance Show Error where
  show = showpp

instance Ex.Exception Error
instance Ex.Exception [Error]

instance ToJSON Error where
  toJSON e = object [ "pos" .= (pos e)
                    , "msg" .= (render $ ppError' Full empty empty e)
                    ]

instance FromJSON Error where
  parseJSON (Object v) = errSaved <$> v .: "pos"
                                  <*> v .: "msg"
  parseJSON _          = mempty

-- type CtxError = Error
--------------------------------------------------------------------------------
ppError :: (PPrint a, SourceInfo s, Show a) => Tidy -> TError s a -> Doc
--------------------------------------------------------------------------------
ppError k e  = ppError' k dSp dCtx e
  where
    dSp      = ppErrSpan (pos e) <> text ": Error:"
    dCtx     = ppErrorCtx e

ppErrSpan :: (SourceInfo s) => s -> Doc
ppErrSpan   = pprint . siSpan

ppErrorCtx :: (SourceInfo s) => TError s a -> Doc
ppErrorCtx   = pprint . siContext . pos

nests n      = foldr (\d acc -> nest n (d $+$ acc)) empty
sepVcat d ds = vcat $ intersperse d ds
blankLine    = sizedText 5 " "

ppFull :: Tidy -> Doc -> Doc
ppFull Full  d = d
ppFull Lossy _ = empty

ppReqInContext :: (PPrint t, PPrint c) => t -> t -> c -> Doc
ppReqInContext tA tE c
  = sepVcat blankLine
      [ nests 2 [ text "Inferred type"
                , text "VV :" <+> pprint tA]
      , nests 2 [ text "not a subtype of Required type"
                , text "VV :" <+> pprint tE]
      , nests 2 [ text "In Context"
                , pprint c                 ]]


ppPropInContext :: (PPrint p, PPrint c) => p -> c -> Doc
ppPropInContext p c
  = sepVcat blankLine
      [ nests 2 [ text "Property"
                , pprint p]
      , nests 2 [ text "Not provable in context"
                , pprint c                 ]]

--------------------------------------------------------------------------------
ppOblig :: Oblig -> Doc
--------------------------------------------------------------------------------
ppOblig OCons = text "Constraint Check"
ppOblig OTerm = text "Termination Check"
ppOblig OInv  = text "Invariant Check"

--------------------------------------------------------------------------------
ppError' :: (PPrint a, Show a, SourceInfo s)
         => Tidy -> Doc -> Doc -> TError s a -> Doc
--------------------------------------------------------------------------------
ppError' td dSp dCtx (ErrAssType _ o _ c p)
  = dSp <+> ppOblig o
        $+$ dCtx
        $+$ (ppFull td $ ppPropInContext p c)

ppError' td dSp dCtx (ErrSubType _ _ c tA tE)
  = dSp <+> text "Liquid Type Mismatch"
        $+$ dCtx
        $+$ (ppFull td $ ppReqInContext tA tE c)

ppError' td  dSp dCtx (ErrFCrash _ _ c tA tE)
  = dSp <+> text "Fixpoint Crash on Constraint"
        $+$ dCtx
        $+$ (ppFull td $ ppReqInContext tA tE c)

ppError' _ dSp dCtx (ErrParse _ _ e)
  = dSp <+> text "Cannot parse specification:"
        $+$ dCtx
        $+$ (nest 4 $ pprint e)

ppError' _ dSp _ (ErrTySpec _ v t s)
  = dSp <+> text "Bad Type Specification"
        $+$ (pprint v <+> dcolon <+> pprint t)
        $+$ (nest 4 $ pprint s)

ppError' _ dSp _ (ErrBadData _ v s)
  = dSp <+> text "Bad Data Specification"
        $+$ (pprint v <+> dcolon <+> pprint s)

ppError' _ dSp dCtx (ErrBadQual _ n d)
  = dSp <+> text "Bad Qualifier Specification for" <+> n
        $+$ dCtx
        $+$ (pprint d)

ppError' _ dSp _ (ErrTermSpec _ v e s)
  = dSp <+> text "Bad Termination Specification"
        $+$ (pprint v <+> dcolon <+> pprint e)
        $+$ (nest 4 $ pprint s)

ppError' _ dSp _ (ErrInvt _ t s)
  = dSp <+> text "Bad Invariant Specification"
        $+$ (nest 4 $ text "invariant " <+> pprint t $+$ pprint s)

ppError' _ dSp _ (ErrIAl _ t s)
  = dSp <+> text "Bad Using Specification"
        $+$ (nest 4 $ text "as" <+> pprint t $+$ pprint s)

ppError' _ dSp _ (ErrIAlMis _ t1 t2 s)
  = dSp <+> text "Incompatible Using Specification"
        $+$ (nest 4 $ (text "using" <+> pprint t1 <+> text "as" <+> pprint t2) $+$ pprint s)

ppError' _ dSp _ (ErrMeas _ t s)
  = dSp <+> text "Bad Measure Specification"
        $+$ (nest 4 $ text "measure " <+> pprint t $+$ pprint s)

ppError' _ dSp _ (ErrHMeas _ t s)
  = dSp <+> text "Cannot promote Haskell function" <+> pprint t <+> text "to logic"
        $+$ (nest 4 $ pprint s)

ppError' _ dSp _ (ErrDupSpecs _ v ls)
  = dSp <+> text "Multiple Specifications for" <+> pprint v <> colon
        $+$ (nest 4 $ vcat $ ppErrSpan <$> ls)

ppError' _ dSp _ (ErrDupAlias _ k v ls)
  = dSp <+> text "Multiple Declarations! "
    $+$ (nest 2 $ text "Multiple Declarations of" <+> pprint k <+> ppVar v $+$ text "Declared at:")
    <+> (nest 4 $ vcat $ ppErrSpan <$> ls)

ppError' _ dSp dCtx (ErrUnbound _ x)
  = dSp <+> text "Unbound variable" <+> pprint x
        $+$ dCtx

ppError' _ dSp dCtx (ErrGhc _ s)
  = dSp <+> text "GHC Error"
        $+$ dCtx
        $+$ (nest 4 $ pprint s)

ppError' _ dSp dCtx (ErrMismatch _ x τ t)
  = dSp <+> text "Specified Type Does Not Refine Haskell Type for" <+> pprint x
        $+$ dCtx
        $+$ text "Haskell:" <+> pprint τ
        $+$ text "Liquid :" <+> pprint t

ppError' _ dSp _ (ErrAliasCycle _ acycle)
  = dSp <+> text "Cyclic Alias Definitions"
        $+$ text "The following alias definitions form a cycle:"
        $+$ (nest 4 $ sepVcat blankLine $ map describe acycle)
  where
    describe (p, name)
      =   text "Type alias:"     <+> pprint name
      $+$ text "Defined at:" <+> ppErrSpan p

ppError' _ dSp dCtx (ErrIllegalAliasApp _ dn dl)
  = dSp <+> text "Refinement Type Alias cannot be used in this context"
        $+$ dCtx
        $+$ text "Type alias:" <+> pprint    dn
        $+$ text "Defined at:" <+> ppErrSpan dl

ppError' _ dSp dCtx (ErrAliasApp _ n name dl dn)
  = dSp <+> text "Malformed Type Alias Application"
        $+$ dCtx
        $+$ text "Type alias:" <+> pprint name
        $+$ text "Defined at:" <+> ppErrSpan dl
        $+$ text "Expects"     <+> pprint dn <+> text "arguments, but is given" <+> pprint n

ppError' _ dSp _ (ErrSaved _ s)
  = dSp <+> s

ppError' _ dSp _ (ErrTermin _ xs s)
  = dSp <+> text "Termination Error"
        <+> (hsep $ intersperse comma $ map pprint xs) $+$ s

ppError' _ dSp _ (ErrRClass p0 c is)
  = dSp <+> text "Refined classes cannot have refined instances"
    $+$ (nest 4 $ sepVcat blankLine $ describeCls : map describeInst is)
  where
    describeCls
      =   text "Refined class definition for:" <+> c
      $+$ text "Defined at:" <+> ppErrSpan p0
    describeInst (p, t)
      =   text "Refined instance for:" <+> t
      $+$ text "Defined at:" <+> ppErrSpan p

ppError' _ dSp dCtx (ErrOther _ s)
  = dSp <+> text "Unexpected panic (!)"
        $+$ dCtx
        $+$ nest 4 (pprint s)

ppVar v = text "`" <> pprint v <> text "'"


--------------------------------------------------------------------------------
-- | Printing Refinement Types -------------------------------------------------
--------------------------------------------------------------------------------

-- MOVE TO TYPES
instance (SubsTy Symbol (RType c Symbol ()) c, TyConable c, Reftable r, PPrint r, PPrint c, FreeVar c Symbol, SubsTy Symbol (RType c Symbol ()) (RType c Symbol ())) => RefTypable c Symbol r where
--   ppCls   = ppClassSymbol
  ppRType = ppr_rtype ppEnv

-- MOVE TO TYPES
instance (Reftable r, PPrint r) => RefTypable RTyCon RTyVar r where
--   ppCls   = ppClassClassPred
  ppRType = ppr_rtype ppEnv

instance Show RTyVar where
  show = showpp

instance PPrint (UReft r) => Show (UReft r) where
  show = showpp

instance (RefTypable c tv r) => PPrint (RType c tv r) where
  pprint = ppRType TopPrec

instance PPrint (RType c tv r) => Show (RType c tv r) where
  show = showpp

instance PPrint (RTProp c tv r) => Show (RTProp c tv r) where
  show = showpp

instance PPrint REnv where
  pprint (REnv m)  = pprint m
