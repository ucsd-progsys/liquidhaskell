
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

-- | This module contains the functions related to @Error@ type,
-- in particular, to @tidyError@ using a solution, and @pprint@ errors.

module Language.Haskell.Liquid.Errors (tidyError) where


import           Control.Applicative                 ((<$>), (<*>))
import           Control.Exception                   (Exception (..))
import           Data.Aeson
import           Data.Hashable
import qualified Data.HashMap.Strict                 as M
import qualified Data.HashSet                        as S
import           Data.List                           (intersperse)
import           Data.Maybe                          (fromMaybe, maybeToList)
import           Data.Monoid                         hiding ((<>))
import           Language.Fixpoint.Misc              hiding (intersperse)
import           Language.Fixpoint.Types             hiding (shiftVV)
import           Language.Haskell.Liquid.PrettyPrint
import           Language.Haskell.Liquid.RefType
import           Language.Haskell.Liquid.Tidy
import           Language.Haskell.Liquid.Types
import           SrcLoc                              (SrcSpan)
import           Text.PrettyPrint.HughesPJ
import           Control.Arrow                       (second)

type Ctx = M.HashMap Symbol SpecType

------------------------------------------------------------------------
tidyError :: FixSolution -> Error -> Error
------------------------------------------------------------------------
tidyError sol 
  = fmap (tidySpecType Full) 
  . tidyErrContext sol
  . applySolution sol

tidyErrContext _ err@(ErrSubType {})
  = err { ctx = c', tact = subst θ tA, texp = subst θ tE }
    where
      (θ, c') = tidyCtx xs $ ctx err 
      xs      = syms tA ++ syms tE
      tA      = tact err
      tE      = texp err

tidyErrContext _ err
  = err

---------------------------------------------------------------------------------
tidyCtx       :: [Symbol] -> Ctx -> (Subst, Ctx) 
---------------------------------------------------------------------------------
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
stripRType t  = (t', ro)
  where
    t'        = fmap (const (uTop mempty)) t
    ro        = stripRTypeBase  t 

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


------------------------------------------------------------------------
-- | Pretty Printing Error Messages ------------------------------------
------------------------------------------------------------------------

-- | Need to put @PPrint Error@ instance here (instead of in Types), 
--   as it depends on @PPrint SpecTypes@, which lives in this module.

instance PPrint Error where
  pprint       = pprintTidy Full
  pprintTidy k = ppError k . fmap ppSpecTypeErr 

ppSpecTypeErr   :: SpecType -> Doc
ppSpecTypeErr t 
  | isTrivial t = dt
  | otherwise   = dt <+> dr 
    where
      dt        = rtypeDoc Lossy t'
      dr        = maybe empty ((text "|" <+>) . pprint) ro 
      (t', ro)  = stripRType t

-- full = isNontrivialVV $ rTypeValueVar t = 

instance Show Error where
  show = showpp

instance Exception Error
instance Exception [Error]

------------------------------------------------------------------------
ppError :: (PPrint a) => Tidy -> TError a -> Doc
------------------------------------------------------------------------

ppError k e  = ppError' k (pprintE $ errSpan e) e
pprintE l    = pprint l <> text ": Error:"

nests n      = foldr (\d acc -> nest n (d $+$ acc)) empty

sepVcat d ds = vcat $ intersperse d ds
blankLine    = sizedText 5 " "

------------------------------------------------------------------------
ppError' :: (PPrint a) => Tidy -> Doc -> TError a -> Doc
-----------------------------------------------------------------------

ppError' _ dSp (ErrAssType _ OCons _ _)
  = dSp <+> text "Constraint Check"

ppError' _ dSp (ErrAssType _ OTerm _ _)
  = dSp <+> text "Termination Check"

ppError' _ dSp (ErrAssType _ OInv _ _)
  = dSp <+> text "Invariant Check"

ppError' Lossy dSp (ErrSubType _ _ _ _ _)
  = dSp <+> text "Liquid Type Mismatch"

ppError' Full  dSp (ErrSubType _ _ c tA tE)
  = dSp <+> text "Liquid Type Mismatch"
        $+$ sepVcat blankLine
              [ nests 2 [ text "Inferred type" 
                        , text "VV :" <+> pprint tA]
              , nests 2 [ text "not a subtype of Required type" 
                        , text "VV :" <+> pprint tE]
              , nests 2 [ text "In Context"
                        , pprint c                 ]]

ppError' _ dSp (ErrParse _ _ e)
  = dSp <+> text "Cannot parse specification:"
    $+$ (nest 4 $ pprint e)

ppError' _ dSp (ErrTySpec _ v t s)
  = dSp <+> text "Bad Type Specification"
    $+$ (pprint v <+> dcolon <+> pprint t)
    $+$ (nest 4 $ pprint s)

ppError' _ dSp (ErrBadData _ v s)
  = dSp <+> text "Bad Data Specification"
    $+$ (pprint v <+> dcolon <+> pprint s)

ppError' _ dSp (ErrTermSpec _ v e s)
  = dSp <+> text "Bad Termination Specification"
    $+$ (pprint v <+> dcolon <+> pprint e)
    $+$ (nest 4 $ pprint s)

ppError' _ dSp (ErrInvt _ t s)
  = dSp <+> text "Bad Invariant Specification"
    $+$ (nest 4 $ text "invariant " <+> pprint t $+$ pprint s)

ppError' _ dSp (ErrIAl _ t s)
  = dSp <+> text "Bad Using Specification"
    $+$ (nest 4 $ text "as" <+> pprint t $+$ pprint s)

ppError' _ dSp (ErrIAlMis _ t1 t2 s)
  = dSp <+> text "Incompatible Using Specification"
    $+$ (nest 4 $ (text "using" <+> pprint t1 <+> text "as" <+> pprint t2) $+$ pprint s)

ppError' _ dSp (ErrMeas _ t s)
  = dSp <+> text "Bad Measure Specification"
    $+$ (nest 4 $ text "measure " <+> pprint t $+$ pprint s)

ppError' _ dSp (ErrHMeas _ t s)
  = dSp <+> text "Cannot promote Haskell function" <+> pprint t <+> text "to logic"
    $+$ (nest 4 $ pprint s)

ppError' _ dSp (ErrDupSpecs _ v ls)
  = dSp <+> text "Multiple Specifications for" <+> pprint v <> colon
    $+$ (nest 4 $ vcat $ pprint <$> ls)

ppError' _ dSp (ErrDupAlias _ k v ls)
  = dSp <+> text "Multiple Declarations! "
    $+$ (nest 2 $ text "Multiple Declarations of" <+> pprint k <+> ppVar v $+$ text "Declared at:")
    <+> (nest 4 $ vcat $ pprint <$> ls)

ppError' _ dSp (ErrUnbound _ x)
  = dSp <+> text "Unbound variable"
    $+$ (nest 4 $ pprint x)

ppError' _ dSp (ErrGhc _ s)
  = dSp <+> text "GHC Error"
    $+$ (nest 4 $ pprint s)

ppError' _ dSp (ErrMismatch _ x τ t)
  = dSp <+> text "Specified Type Does Not Refine Haskell Type for" <+> pprint x
    $+$ text "Haskell:" <+> pprint τ
    $+$ text "Liquid :" <+> pprint t

ppError' _ dSp (ErrAliasCycle _ acycle)
  = dSp <+> text "Cyclic Refined Type Alias Definitions"
    $+$ text "The following alias definitions form a cycle:"
    $+$ (nest 4 $ sepVcat blankLine $ map describe acycle)
  where
    describe (pos, name)
      = text "Type alias:"     <+> pprint name
        $+$ text "Defined at:" <+> pprint pos

ppError' _ dSp (ErrIllegalAliasApp _ dn dl)
  = dSp <+> text "Refinement Type Alias cannot be used in this context"
    $+$ text "Type alias:" <+> pprint dn
    $+$ text "Defined at:" <+> pprint dl

ppError' _ dSp (ErrAliasApp _ n name dl dn)
  = dSp <+> text "Malformed Type Alias Application"
    $+$ text "Type alias:" <+> pprint name
    $+$ text "Defined at:" <+> pprint dl
    $+$ text "Expects"     <+> pprint dn <+> text "arguments, but is given" <+> pprint n  

ppError' _ dSp (ErrSaved _ s)
  = dSp <+> s

ppError' _ dSp (ErrTermin xs _ s)
  = dSp <+> text "Termination Error on" <+> (hsep $ intersperse comma $ map pprint xs) $+$ s

ppError' _ dSp (ErrRClass pos cls insts)
  = dSp <+> text "Refined classes cannot have refined instances"
    $+$ (nest 4 $ sepVcat blankLine $ describeCls : map describeInst insts)
  where
    describeCls
      = text "Refined class definition for:" <+> cls
        $+$ text "Defined at:" <+> pprint pos
    describeInst (pos, t)
      = text "Refined instance for:" <+> t
        $+$ text "Defined at:" <+> pprint pos

ppError' _ _ (ErrOther _ s)
  = text "Panic!" <+> nest 4 (pprint s)


ppVar v = text "`" <> pprint v <> text "'"


instance ToJSON Error where
  toJSON e = object [ "pos" .= (errSpan e)
                    , "msg" .= (render $ ppError' Full empty e)
                    ]

instance FromJSON Error where
  parseJSON (Object v) = errSaved <$> v .: "pos"
                                  <*> v .: "msg"
  parseJSON _          = mempty


errSaved :: SrcSpan -> String -> Error
errSaved x = ErrSaved x . text
