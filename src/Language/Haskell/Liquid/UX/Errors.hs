{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

-- | This module contains the functions related to @Error@ type,
-- in particular, to @tidyError@ using a solution, and @pprint@ errors.

module Language.Haskell.Liquid.UX.Errors
  ( -- * Cleanup an Error
    tidyError

    -- * Various ways to die
  , panic
  , panicError
  , todo
  , impossible
  ) where

import           Control.Arrow                       (second)
import           Control.Exception                   (Exception (..))
import           Data.Aeson
import           Data.Generics                       (everywhere, mkT)
import qualified Data.HashMap.Strict                 as M
import qualified Data.HashSet                        as S
import qualified Data.Text                           as T
import           Data.Hashable
import           Data.List                           (intersperse)
import           Data.Maybe                          (fromMaybe, maybeToList)
import           Language.Fixpoint.Misc              (dcolon)
import           Language.Fixpoint.Types             hiding (Error, SrcSpan, shiftVV)
import           Language.Haskell.Liquid.UX.PrettyPrint
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Transforms.Simplify
import           Language.Haskell.Liquid.UX.Tidy
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Misc        (single)
import           SrcLoc                              (SrcSpan)
import           Text.PrettyPrint.HughesPJ
import qualified Control.Exception as Ex
-- import           System.Console.ANSI

type Ctx = M.HashMap Symbol SpecType

------------------------------------------------------------------------
tidyError :: FixSolution -> Error -> Error
------------------------------------------------------------------------
tidyError sol
  = fmap (tidySpecType Full)
  . tidyErrContext sol
  . applySolution sol

tidyErrContext :: FixSolution -> TError s SpecType -> TError s SpecType
tidyErrContext _ e@(ErrSubType {})
  = e { ctx = c', tact = subst θ tA, texp = subst θ tE }
    where
      (θ, c') = tidyCtx xs $ ctx e
      xs      = syms tA ++ syms tE
      tA      = tact e
      tE      = texp e

tidyErrContext _ e@(ErrAssType {})
  = e { ctx = c', cond = subst θ p }
    where
      (θ, c') = tidyCtx xs $ ctx e
      xs      = syms p
      p       = cond e

tidyErrContext _ e
  = e

--------------------------------------------------------------------------------
tidyCtx       :: [Symbol] -> Ctx -> (Subst, Ctx)
--------------------------------------------------------------------------------
tidyCtx xs m  = (θ, M.fromList yts)
  where
    yts       = [tBind x t | (x, t) <- xts]
    (θ, xts)  = tidyTemps $ second stripReft <$> tidyREnv xs m
    tBind x t = (x', shiftVV t x') where x' = tidySymbol x


stripReft     :: SpecType -> SpecType
stripReft t   = maybe t' (strengthen t') ro
  where
    (t', ro)  = stripRType t

stripRType    :: SpecType -> (SpecType, Maybe RReft)
stripRType st = (t', ro)
  where
    t'        = fmap (const (uTop mempty)) t
    ro        = stripRTypeBase  t
    t         = simplifyBounds st

tidyREnv      :: [Symbol] -> M.HashMap Symbol SpecType -> [(Symbol, SpecType)]
tidyREnv xs m = [(x, t) | x <- xs', t <- maybeToList (M.lookup x m), ok t]
  where
    xs'       = expandFix deps xs
    deps y    = fromMaybe [] $ fmap (syms . rTypeReft) $ M.lookup y m
    ok        = not . isFunTy

expandFix :: (Eq a, Hashable a) => (a -> [a]) -> [a] -> [a]
expandFix f xs            = S.toList $ go S.empty xs
  where
    go seen []            = seen
    go seen (x:xs)
      | x `S.member` seen = go seen xs
      | otherwise         = go (S.insert x seen) (f x ++ xs)

tidyTemps     :: (Subable t) => [(Symbol, t)] -> (Subst, [(Symbol, t)])
tidyTemps xts = (θ, [(txB x, txTy t) | (x, t) <- xts])
  where
    txB  x    = M.lookupDefault x x m
    txTy      = subst θ
    m         = M.fromList yzs
    θ         = mkSubst [(y, EVar z) | (y, z) <- yzs]
    yzs       = zip ys niceTemps
    ys        = [ x | (x,_) <- xts, isTmpSymbol x]

niceTemps     :: [Symbol]
niceTemps     = mkSymbol <$> xs ++ ys
  where
    mkSymbol  = symbol . ('?' :)
    xs        = single   <$> ['a' .. 'z']
    ys        = ("a" ++) <$> [show n | n <- [0 ..]]

--------------------------------------------------------------------------------
-- | Context information for Error Messages ------------------------------------
--------------------------------------------------------------------------------

class SourceInfo s where
  siSpan    :: s -> SrcSpan
  siContext :: s -> Doc

instance SourceInfo SrcSpan where
  siSpan x    = x
  siContext _ = empty


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

instance Exception Error
instance Exception [Error]

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

------------------------------------------------------------------------
-- | Errors ------------------------------------------------------------
------------------------------------------------------------------------

-- | Show an Error, then crash
panicError :: {-(?callStack :: CallStack) =>-} Error -> a
panicError = Ex.throw

-- | Construct and show an Error, then crash
panic :: {-(?callStack :: CallStack) =>-} Maybe SrcSpan -> String -> a
panic sp d = panicError $ errOther sp $ text d

-- | Construct and show an Error with no SrcSpan, then crash
--   This function should be used to mark unimplemented functionality
todo :: {-(?callStack :: CallStack) =>-} String -> a
todo m = panic Nothing $ "TODO: " ++ m

-- | Construct and show an Error with no SrcSpan, then crash
--   This function should be used to mark impossible-to-reach codepaths
impossible :: {-(?callStack :: CallStack) =>-} String -> a
impossible  m = panic Nothing $ "Should never happen: " ++ m
