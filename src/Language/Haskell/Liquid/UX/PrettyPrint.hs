{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TupleSections        #-}

-- | Module with PPrint instances

module Language.Haskell.Liquid.UX.PrettyPrint (
  -- * Printing Lists (TODO: move to fixpoint)
    pprManyOrdered
  , pprintLongList
  , pprintSymbol
  ) where

import ErrUtils                         (ErrMsg)
import HscTypes                         (SourceError)
import SrcLoc
import GHC                              (Name, Class)
import TypeRep          hiding (maybeParen, pprArrowChain)
import Var              (Var)
import TyCon            (TyCon)

import Data.Generics                       (everywhere, mkT)

-- import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.GHC.Misc
import Language.Fixpoint.Types hiding (Error, SrcSpan, Predicate)
import Language.Fixpoint.Misc hiding (intersperse)
import Language.Haskell.Liquid.Types hiding (sort)
import Language.Haskell.Liquid.Types.RTDoc
import Language.Haskell.Liquid.UX.Tidy

import Text.Parsec.Error (ParseError, errorMessages, showErrorMessages)
import Text.PrettyPrint.HughesPJ

-- import Data.Maybe   (fromMaybe)
import Data.List    (intersperse, sort)
-- import Data.Function (on)
import Data.Aeson

import qualified Control.Exception  as Ex
import qualified Data.HashMap.Strict as M



--------------------------------------------------------------------------------
pprManyOrdered :: (PPrint a, Ord a) => Tidy -> String -> [a] -> [Doc]
--------------------------------------------------------------------------------
pprManyOrdered k msg = map ((text msg <+>) . pprintTidy k) . sort

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

instance PPrint SrcSpan where
  pprint = pprDoc

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

errSaved :: SrcSpan -> String -> Error
errSaved x = ErrSaved x . text

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
