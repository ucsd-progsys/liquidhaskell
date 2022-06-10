-- | This module contains a single function that converts a RType -> Doc
--   without using *any* simplifications.

{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MonoLocalBinds       #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE ScopedTypeVariables  #-}

{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Haskell.Liquid.Types.PrettyPrint
  ( -- * Printable RTypes
    OkRT

    -- * Printers
  , rtypeDoc

  -- * Printing Lists (TODO: move to fixpoint)
  , pprManyOrdered
  , pprintLongList
  , pprintSymbol

  -- * Printing diagnostics
  , printWarning
  , printError

  -- * Filtering errors
  , Filter(..)
  , getFilters
  , reduceFilters
  , defaultFilterReporter

  -- * Reporting errors in the typechecking phase
  , FilterReportErrorsArgs(..)
  , filterReportErrorsWith
  , filterReportErrors

  ) where

import           Control.Monad                           (void)
import qualified Data.HashMap.Strict              as M
import qualified Data.List                        as L                               -- (sort)
import qualified Data.Set                         as Set
import           Data.String
import           Language.Fixpoint.Misc
import qualified Language.Fixpoint.Types          as F
import qualified Language.Haskell.Liquid.GHC.API  as Ghc
import           Language.Haskell.Liquid.GHC.API  as Ghc ( Class
                                                         , SrcSpan
                                                         , PprPrec
                                                         , DynFlags
                                                         , Type
                                                         , Var
                                                         , Name
                                                         , ErrMsg
                                                         , SourceError
                                                         , TyCon
                                                         , topPrec
                                                         , funPrec
                                                         , srcSpanStartLine
                                                         , srcSpanStartCol
                                                         )
import           Language.Haskell.Liquid.GHC.Logging (putErrMsg, mkLongErrAt)
import           Language.Haskell.Liquid.GHC.Misc
import           Language.Haskell.Liquid.Misc
import           Language.Haskell.Liquid.Types.Types
import           Prelude                          hiding (error)
import           Text.PrettyPrint.HughesPJ        hiding ((<>))

data Filter = StringFilter String
            | AnyFilter
  deriving (Eq, Ord, Show)

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
pprintSymbol x = char '‘' <-> pprint x <-> char '’'


--------------------------------------------------------------------------------
-- | A whole bunch of PPrint instances follow ----------------------------------
--------------------------------------------------------------------------------
instance PPrint ErrMsg where
  pprintTidy _ = text . show

instance PPrint SourceError where
  pprintTidy _ = text . show

instance PPrint Var where
  pprintTidy _ = pprDoc

instance PPrint (Ghc.Expr Var) where
  pprintTidy _ = pprDoc

instance PPrint (Ghc.Bind Var) where
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
pprAnnInfoBind k (Ghc.RealSrcSpan sp _, xv)
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
  -- pprintTidy _ = ppRType topPrec

instance (PPrint tv, PPrint ty) => PPrint (RTAlias tv ty) where
  pprintTidy = ppAlias

ppAlias :: (PPrint tv, PPrint ty) => F.Tidy -> RTAlias tv ty -> Doc
ppAlias k a =   pprint (rtName a)
            <+> pprints k space (rtTArgs a)
            <+> pprints k space (rtVArgs a)
            <+> text " = "
            <+> pprint (rtBody a)

instance (F.PPrint tv, F.PPrint t) => F.PPrint (RTEnv tv t) where
  pprintTidy k rte
    =   text "** Type Aliaes *********************"
    $+$ nest 4 (F.pprintTidy k (typeAliases rte))
    $+$ text "** Expr Aliases ********************"
    $+$ nest 4 (F.pprintTidy k (exprAliases rte))

pprints :: (PPrint a) => F.Tidy -> Doc -> [a] -> Doc
pprints k c = sep . punctuate c . map (pprintTidy k)

--------------------------------------------------------------------------------
rtypeDoc :: (OkRT c tv r) => F.Tidy -> RType c tv r -> Doc
--------------------------------------------------------------------------------
rtypeDoc k      = ppr_rtype (ppE k) topPrec
  where
    ppE F.Lossy = ppEnvShort ppEnv
    ppE F.Full  = ppEnv

instance PPrint F.Tidy where
  pprintTidy _ F.Full  = "Full"
  pprintTidy _ F.Lossy = "Lossy"

type Prec = PprPrec

--------------------------------------------------------------------------------
ppr_rtype :: (OkRT c tv r) => PPEnv -> Prec -> RType c tv r -> Doc
--------------------------------------------------------------------------------
ppr_rtype bb p t@(RAllT _ _ r)
  = F.ppTy r $ ppr_forall bb p t
ppr_rtype bb p t@(RAllP _ _)
  = ppr_forall bb p t
ppr_rtype _ _ (RVar a r)
  = F.ppTy r $ pprint a
ppr_rtype bb p t@(RImpF _ _ _ _ _)
  = maybeParen p funPrec (ppr_rty_fun bb empty t)
ppr_rtype bb p t@(RFun _ _ _ _ _)
  = maybeParen p funPrec (ppr_rty_fun bb empty t)
ppr_rtype bb p (RApp c [t] rs r)
  | isList c
  = F.ppTy r $ brackets (ppr_rtype bb p t) <-> ppReftPs bb p rs
ppr_rtype bb p (RApp c ts rs r)
  | isTuple c
  = F.ppTy r $ parens (intersperse comma (ppr_rtype bb p <$> ts)) <-> ppReftPs bb p rs
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
  | ppShort bb = {- shortModules . -} ppTycon
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
    pprint_bind (x, t) = pprint x <+> colon <-> colon <+> ppr_rtype bb p t
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
  = text "exists" <+> brackets (intersperse comma [ppr_dbind bb topPrec x t | (x, t) <- zs]) <-> dot <-> ppr_rtype bb p t'
    where (zs,  t')               = split [] t
          split zs (REx x t t')   = split ((x,t):zs) t'
          split zs t                = (reverse zs, t)

ppAllExpr
  :: (OkRT c tv r, PPrint (RType c tv r), PPrint (RType c tv ()))
  => PPEnv -> Prec -> RType c tv r -> Doc
ppAllExpr bb p t
  = text "forall" <+> brackets (intersperse comma [ppr_dbind bb topPrec x t | (x, t) <- zs]) <-> dot <-> ppr_rtype bb p t'
    where 
      (zs,  t')               = split [] t
      split zs (RAllE x t t') = split ((x,t):zs) t'
      split zs t              = (reverse zs, t)

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
  = pprint x <-> colon <-> ppr_rtype bb p t



ppr_rty_fun
  :: ( OkRT c tv r, PPrint (RType c tv r), PPrint (RType c tv ()))
  => PPEnv -> Doc -> RType c tv r -> Doc
ppr_rty_fun bb prefix t = hsep (prefix : dArgs ++ [dOut])
  where
    dArgs               = concatMap ppArg args
    dOut                = ppr_rtype bb topPrec out
    ppArg (b, t, a)     = [ppr_dbind bb funPrec b t, a]
    (args, out)         = brkFun t

{- 
ppr_rty_fun bb prefix t
  = prefix <+> ppr_rty_fun' bb t

ppr_rty_fun'
  :: ( OkRT c tv r, PPrint (RType c tv r), PPrint (RType c tv ()))
  => PPEnv -> RType c tv r -> Doc
ppr_rty_fun' bb (RImpF b t t' r)
  = F.ppTy r $ ppr_dbind bb funPrec b t $+$ ppr_rty_fun bb (text "~>") t'
ppr_rty_fun' bb (RFun b t t' r)
  = F.ppTy r $ ppr_dbind bb funPrec b t $+$ ppr_rty_fun bb arrow t'
ppr_rty_fun' bb t
  = ppr_rtype bb topPrec t
-}

brkFun :: RType c tv r -> ([(F.Symbol, RType c tv r, Doc)], RType c tv r)
brkFun (RImpF b _ t t' _) = ((b, t, (text "~>")) : args, out)   where (args, out)     = brkFun t'
brkFun (RFun b _ t t' _)  = ((b, t, (text "->")) : args, out)   where (args, out)     = brkFun t'
brkFun out                = ([], out)




ppr_forall :: (OkRT c tv r) => PPEnv -> Prec -> RType c tv r -> Doc
ppr_forall bb p t = maybeParen p funPrec $ sep [
                      ppr_foralls (ppPs bb) (fst <$> ty_vars trep) (ty_preds trep)
                    , ppr_clss cls
                    , ppr_rtype bb topPrec t'
                    ]
  where
    trep          = toRTypeRep t
    -- YL: remember to revert back
    (cls, t')     = bkClass $ fromRTypeRep $ trep {ty_vars = [], ty_preds = []}
    -- t' = fromRTypeRep $ trep {ty_vars = [], ty_preds = []}

    ppr_foralls False _ _  = empty
    ppr_foralls _    [] [] = empty
    ppr_foralls True αs πs = text "forall" <+> dαs αs <+> dπs (ppPs bb) πs <-> dot

    ppr_clss []               = empty
    ppr_clss cs               = (parens $ hsep $ punctuate comma (uncurry (ppr_cls bb p) <$> cs)) <+> text "=>"

    dαs αs                    = ppr_rtvar_def αs

    -- dπs :: Bool -> [PVar a] -> Doc
    dπs _ []                  = empty
    dπs False _               = empty
    dπs True πs               = angleBrackets $ intersperse comma $ ppr_pvar_def bb p <$> πs

ppr_rtvar_def :: (PPrint tv) => [RTVar tv (RType c tv ())] -> Doc
ppr_rtvar_def = sep . map (pprint . ty_var_value)

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
ppRefArgs ss = text "\\" <-> hsep (ppRefSym <$> ss ++ [F.vv Nothing]) <+> arrow

ppRefSym :: (Eq a, IsString a, PPrint a) => a -> Doc
ppRefSym "" = text "_"
ppRefSym s  = pprint s

dot :: Doc
dot                = char '.'

instance (PPrint r, F.Reftable r) => PPrint (UReft r) where
  pprintTidy k (MkUReft r p)
    | F.isTauto r  = pprintTidy k p
    | F.isTauto p  = pprintTidy k r
    | otherwise  = pprintTidy k p <-> text " & " <-> pprintTidy k r

--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- | Pretty-printing errors ----------------------------------------------------
--------------------------------------------------------------------------------

printError :: (Show e, F.PPrint e) => F.Tidy -> DynFlags -> TError e -> IO ()
printError k dyn err = putErrMsg dyn (pos err) (ppError k empty err)

-- | Similar in spirit to 'reportErrors' from the GHC API, but it uses our
-- pretty-printer and shim functions under the hood. Also filters the errors
-- according to the given `Filter` list.
--
-- @filterReportErrors failure continue filters k@ will call @failure@ if there
-- are unexpected errors, or will call @continue@ otherwise.
--
-- An error is expected if there is any filter that matches it.
filterReportErrors :: forall e' a. (Show e', F.PPrint e') => FilePath -> Ghc.TcRn a -> Ghc.TcRn a -> [Filter] -> F.Tidy -> [TError e'] -> Ghc.TcRn a
filterReportErrors path failure continue filters k =
  filterReportErrorsWith
    FilterReportErrorsArgs { msgReporter = Ghc.reportErrors
                           , filterReporter = defaultFilterReporter path
                           , failure = failure
                           , continue = continue
                           , pprinter = \err -> mkLongErrAt (pos err) (ppError k empty err) mempty
                           , filterMapper = reduceFilters renderer filters
                           , filters = filters
                           }
  where
    renderer :: TError e' -> String
    renderer = render . ppError k empty

-- | Retrieve the `Filter`s from the Config.
getFilters :: Config -> [Filter]
getFilters cfg = anyFilter <> stringFilters
  where
    anyFilter = [AnyFilter | expectAnyError cfg]
    stringFilters = StringFilter <$> expectErrorContaining cfg

-- | Return either the error as a singleton or the list of @filters@ that
-- matched the @err@, given a @renderer@ for the @err@ and some @filters@
reduceFilters :: forall e. (e -> String) -> [Filter] -> e -> Either [e] [Filter]
reduceFilters renderer fs err =
  if null matchingFilters
  then Left [err]
  else Right matchingFilters
  where
    matchingFilters :: [Filter]
    matchingFilters = filter (filterDoesMatchErr err) fs

    filterDoesMatchErr :: e -> Filter -> Bool
    filterDoesMatchErr _ AnyFilter = True
    filterDoesMatchErr e (StringFilter filter) = filter `L.isInfixOf` renderer e

-- | Used in `filterReportErrorsWith'`
data FilterReportErrorsArgs m filter msg e a =
  FilterReportErrorsArgs
  { msgReporter :: [msg] -> m ()
  , filterReporter :: [filter] -> m ()
  , failure :: m a
  , continue :: m a
  , pprinter :: e -> m msg
  , filterMapper :: e -> Either [e] [filter]
  , filters :: [filter]
  }

-- | Abstract filtered error reporter
filterReportErrorsWith :: (Monad m, Ord filter) => FilterReportErrorsArgs m filter msg e a -> [e] -> m a
filterReportErrorsWith FilterReportErrorsArgs {..} errs =
  let
    reducedErrs = concat <$> traverse filterMapper errs
    wasExactlyFiltered =
      case reducedErrs of
        Left es -> null es
        Right fs -> Set.fromList filters == Set.fromList fs
  in
    if wasExactlyFiltered
    then continue
    else do
      case reducedErrs of
        Left es -> do
          msgs <- traverse pprinter es
          void $ msgReporter msgs
        Right fs -> do
          let missedFilters = Set.toList $ Set.fromList filters `Set.difference` Set.fromList fs
          filterReporter missedFilters
      failure

-- | Report errors via GHC's API stating the given `Filter`s did not get
-- matched. Does nothing if the list of filters is empty.
defaultFilterReporter :: FilePath -> [Filter] -> Ghc.TcRn ()
defaultFilterReporter _ [] = pure ()
defaultFilterReporter path fs = Ghc.reportError =<< mkLongErrAt srcSpan (vcat $ leaderMsg : (nest 4 <$> filterMsgs)) empty
  where
    leaderMsg :: Doc
    leaderMsg = text "Could not match the following expected errors with actual thrown errors:"

    filterToMsg :: Filter -> Doc
    filterToMsg AnyFilter = text "<Any Liquid error>"
    filterToMsg (StringFilter s) = text "String filter: " <-> quotes (text s)

    filterMsgs :: [Doc]
    filterMsgs = filterToMsg <$> fs

    beginningOfFile :: Ghc.SrcLoc
    beginningOfFile = Ghc.mkSrcLoc (fromString path) 1 1

    srcSpan :: SrcSpan
    srcSpan = Ghc.mkSrcSpan beginningOfFile beginningOfFile
