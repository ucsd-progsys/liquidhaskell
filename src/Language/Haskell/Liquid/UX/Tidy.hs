
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams    #-}

---------------------------------------------------------------------
-- | This module contains functions for cleaning up types before
--   they are rendered, e.g. in error messages or annoations,
--   and also some PPrint instances that rely upon tidying.
---------------------------------------------------------------------

module Language.Haskell.Liquid.UX.Tidy (

    -- * Tidying functions
    tidySpecType
  , tidySymbol

    -- * Tidyness tests
  , isTmpSymbol

    -- * Panic and Exit
  , panicError
  ) where

import qualified Data.HashMap.Strict as M
import qualified Data.HashSet        as S
import qualified Data.List           as L
import qualified Data.Text           as T
import           Data.Maybe                 (fromMaybe)
import           Data.Aeson
import qualified Control.Exception  as Ex

import Language.Haskell.Liquid.GHC.Misc      (stringTyVar)
import Language.Fixpoint.Types      hiding (SrcSpan, Error)
import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.Types.RefType (rVar, subsTyVars_meet)
import Language.Haskell.Liquid.Types.PrettyPrint
import Language.Fixpoint.Misc hiding (intersperse)

import SrcLoc
import Data.List    (intersperse )
import Data.Generics                       (everywhere, mkT)
import Language.Haskell.Liquid.Types.PrettyPrint ()
import Text.PrettyPrint.HughesPJ

-------------------------------------------------------------------------
isTmpSymbol    :: Symbol -> Bool
-------------------------------------------------------------------------
isTmpSymbol x  = any (`isPrefixOfSym` x) [anfPrefix, tempPrefix, "ds_"]

-------------------------------------------------------------------------
tidySpecType :: Tidy -> SpecType -> SpecType
-------------------------------------------------------------------------
tidySpecType k = tidyValueVars
               . tidyDSymbols
               . tidySymbols
               . tidyLocalRefas k
               . tidyFunBinds
               . tidyTyVars

tidyValueVars :: SpecType -> SpecType
tidyValueVars = mapReft $ \u -> u { ur_reft = tidyVV $ ur_reft u }

tidyVV r@(Reft (va,_))
  | isJunk va = shiftVV r v'
  | otherwise = r
  where
    v'        = if v `elem` xs then symbol ("v'" :: T.Text) else v
    v         = symbol ("v" :: T.Text)
    xs        = syms r
    isJunk    = isPrefixOfSym "x"

tidySymbols :: SpecType -> SpecType
tidySymbols t = substa tidySymbol $ mapBind dropBind t
  where
    xs         = S.fromList (syms t)
    dropBind x = if x `S.member` xs then tidySymbol x else nonSymbol


tidyLocalRefas   :: Tidy -> SpecType -> SpecType
tidyLocalRefas k = mapReft (txStrata . txReft' k)
  where
    txReft' Full                  = id
    txReft' Lossy                 = txReft
    txStrata (MkUReft r p l)      = MkUReft r p (txStr l)
    txReft u                      = u { ur_reft = mapPredReft dropLocals $ ur_reft u }
    dropLocals                    = pAnd . filter (not . any isTmp . syms) . conjuncts
    isTmp x                       = any (`isPrefixOfSym` x) [anfPrefix, "ds_"]
    txStr                         = filter (not . isSVar)

tidyDSymbols :: SpecType -> SpecType
tidyDSymbols t = mapBind tx $ substa tx t
  where
    tx         = bindersTx [x | x <- syms t, isTmp x]
    isTmp      = (tempPrefix `isPrefixOfSym`)

tidyFunBinds :: SpecType -> SpecType
tidyFunBinds t = mapBind tx $ substa tx t
  where
    tx         = bindersTx $ filter isTmpSymbol $ funBinds t

tidyTyVars :: SpecType -> SpecType
tidyTyVars t = subsTyVarsAll αβs t
  where
    αβs  = zipWith (\α β -> (α, toRSort β, β)) αs βs
    αs   = L.nub (tyVars t)
    βs   = map (rVar . stringTyVar) pool
    pool = [[c] | c <- ['a'..'z']] ++ [ "t" ++ show i | i <- [1..]]


bindersTx ds   = \y -> M.lookupDefault y y m
  where
    m          = M.fromList $ zip ds $ var <$> [1..]
    var        = symbol . ('x' :) . show


tyVars (RAllP _ t)     = tyVars t
tyVars (RAllS _ t)     = tyVars t
tyVars (RAllT α t)     = α : tyVars t
tyVars (RFun _ t t' _) = tyVars t ++ tyVars t'
tyVars (RAppTy t t' _) = tyVars t ++ tyVars t'
tyVars (RApp _ ts _ _) = concatMap tyVars ts
tyVars (RVar α _)      = [α]
tyVars (RAllE _ _ t)   = tyVars t
tyVars (REx _ _ t)     = tyVars t
tyVars (RExprArg _)    = []
tyVars (RRTy _ _ _ t)  = tyVars t
tyVars (RHole _)       = []

subsTyVarsAll ats = go
  where
    abm            = M.fromList [(a, b) | (a, _, (RVar b _)) <- ats]
    go (RAllT a t) = RAllT (M.lookupDefault a a abm) (go t)
    go t           = subsTyVars_meet ats t


funBinds (RAllT _ t)      = funBinds t
funBinds (RAllP _ t)      = funBinds t
funBinds (RAllS _ t)      = funBinds t
funBinds (RFun b t1 t2 _) = b : funBinds t1 ++ funBinds t2
funBinds (RApp _ ts _ _)  = concatMap funBinds ts
funBinds (RAllE b t1 t2)  = b : funBinds t1 ++ funBinds t2
funBinds (REx b t1 t2)    = b : funBinds t1 ++ funBinds t2
funBinds (RVar _ _)       = []
funBinds (RRTy _ _ _ t)   = funBinds t
funBinds (RAppTy t1 t2 _) = funBinds t1 ++ funBinds t2
funBinds (RExprArg _)     = []
funBinds (RHole _)        = []


--------------------------------------------------------------------------------
-- | Show an Error, then crash
--------------------------------------------------------------------------------
panicError :: {-(?callStack :: CallStack) =>-} Error -> a
--------------------------------------------------------------------------------
panicError = Ex.throw

-- ^ This function is put in this module as
--   it depends on the Exception instance,
--   which depends on the PPrint instance,
--   which depends on tidySpecType.

--------------------------------------------------------------------------------
-- | Pretty Printing Error Messages --------------------------------------------
--------------------------------------------------------------------------------

-- | Need to put @PPrint Error@ instance here (instead of in Types),
--   as it depends on @PPrint SpecTypes@, which lives in this module.

instance PPrint (CtxError SpecType) where
  pprint          = pprintTidy Full
  pprintTidy k ce = ppError k (ctCtx ce) $ ppSpecTypeErr <$> ctErr ce

instance PPrint Error where
  pprint       = pprintTidy Full
  pprintTidy k = ppError k empty . fmap ppSpecTypeErr

ppSpecTypeErr :: SpecType -> Doc
ppSpecTypeErr = rtypeDoc     Lossy
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
ppError :: (PPrint a, Show a) => Tidy -> Doc -> TError a -> Doc
--------------------------------------------------------------------------------
ppError k dCtx e = ppError' k dSp dCtx e
  where
    dSp          = pprint (pos e) <> text ": Error:"

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

{-
pprintCtx :: (PTable c) => c -> Doc
pprintCtx = pprint . ptable

instance (PPrint a, PPrint b) => PTable (M.HashMap a b) where
  ptable t = DocTable [ (pprint k, pprint v) | (k, v) <- M.toList t]


pprintKVs :: (PPrint k, PPrint v) => [(k, v)] -> Doc
pprintKVs = vcat . punctuate (text "\n") . map pp1
  where
    pp1 (x,y) = pprint x <+> text ":=" <+> pprint y
-}

--------------------------------------------------------------------------------
ppError' :: (PPrint a, Show a) => Tidy -> Doc -> Doc -> TError a -> Doc
--------------------------------------------------------------------------------
ppError' td dSp dCtx (ErrAssType _ o _ c p)
  = dSp <+> pprint o
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
        $+$ (nest 4 $ vcat $ pprint <$> ls)

ppError' _ dSp _ (ErrDupAlias _ k v ls)
  = dSp <+> text "Multiple Declarations! "
    $+$ (nest 2 $ text "Multiple Declarations of" <+> pprint k <+> ppVar v $+$ text "Declared at:")
    <+> (nest 4 $ vcat $ pprint <$> ls)

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
    describe (p, n)
      =   text "Type alias:" <+> pprint n
      $+$ text "Defined at:" <+> pprint p

ppError' _ dSp dCtx (ErrIllegalAliasApp _ dn dl)
  = dSp <+> text "Refinement Type Alias cannot be used in this context"
        $+$ dCtx
        $+$ text "Type alias:" <+> pprint dn
        $+$ text "Defined at:" <+> pprint dl

ppError' _ dSp dCtx (ErrAliasApp _ n name dl dn)
  = dSp <+> text "Malformed Type Alias Application"
        $+$ dCtx
        $+$ text "Type alias:" <+> pprint name
        $+$ text "Defined at:" <+> pprint dl
        $+$ text "Expects"     <+> pprint dn <+> text "arguments, but is given" <+> pprint n

ppError' _ dSp _ (ErrSaved _ s)
  = dSp <+> s

ppError' _ dSp dCtx (ErrOther _ s)
  = dSp <+> text "Uh oh."
        $+$ dCtx
        $+$ nest 4 s

ppError' _ dSp _ (ErrTermin _ xs s)
  = dSp <+> text "Termination Error"
        <+> (hsep $ intersperse comma $ map pprint xs) $+$ s

ppError' _ dSp _ (ErrRClass p0 c is)
  = dSp <+> text "Refined classes cannot have refined instances"
    $+$ (nest 4 $ sepVcat blankLine $ describeCls : map describeInst is)
  where
    describeCls
      =   text "Refined class definition for:" <+> c
      $+$ text "Defined at:" <+> pprint p0
    describeInst (p, t)
      =   text "Refined instance for:" <+> t
      $+$ text "Defined at:" <+> pprint p

ppVar v = text "`" <> pprint v <> text "'"
