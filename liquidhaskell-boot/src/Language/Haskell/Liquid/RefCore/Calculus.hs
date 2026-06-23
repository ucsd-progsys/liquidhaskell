{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Grammars, printer and suable functions for ILH
module Language.Haskell.Liquid.RefCore.Calculus
  ( -- * Grammar
    Builtin (..),
    BaseType (..),
    RefType (..),
    Decl (..),
    Expr (..),
    Reft (..),
    ProjKind (..),
    Localization (..),
    DesState (..),
    Bop (..),
    ProofOp (..),

    -- * Builtin type and data constructors
    boolTp,
    ttTm,
    ffTm,
    unitTp,
    unitTm,

    -- * Construction and destruction
    mkVar,
    arrs,
    apps,
    renameParams,

    -- * Free variables and substitution
    HasVars (..),
    freeVars,
    fresh,
    rename,
    substs,
  )
where

import Data.Bifunctor (first)
import Data.Binary (Binary)
import Data.Data
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Generics (Generic)
import Language.Haskell.Liquid.RefCore.Names (Id, boolTpName, ffTmName, freshVar, ttTmName, unitTmName, unitTpName)
import Text.PrettyPrint
import Text.PrettyPrint.HughesPJClass hiding (first)
import Prelude hiding (lookup, (<>))

-- * The grammar

-- ** Types

-- | Builtin types
-- In Fixpoint, we have the Constant types Integer, Double and Text. There, from GHC.Core,
-- Floats are stored as Double, and Chars and Strings are converted to Text (we switch back to
-- Strings for simplicity). Other GHC.Core literals are not relevant for us
--
-- > B ::= Integer | Double | String
data Builtin = Integer | Double | String deriving (Data, Eq, Show, Generic, Binary)

-- | Base Types
--
-- > A ::= B | TC
data BaseType = Builtin Builtin | TC Id deriving (Data, Eq, Show, Generic, Binary)

-- | Refinement types
--
-- > R ::= {x: A | r} | x:Rx -> R
data RefType
  = RefType Id BaseType Reft
  | ArrType Id RefType RefType
  deriving (Data, Show, Generic, Binary)

-- ** Declaration-level grammar

-- | Declarations
--
-- > D ::= data tc := (C :: R)*
-- >     | (reflect)? def f :: R := e
data Decl
  = -- | type constructor: name and branches with (constructor name, type)
    Data Id [(Id, RefType)]
  | -- | (function) definition: name, type, body, is it reflected
    Definition Id RefType Expr Bool
  | -- | imported module: module name and its declarations
    Import Id [Decl]
  deriving (Data, Eq, Show, Generic, Binary)

-- | Structural expressions
--
-- > e ::= r
-- >     | let x (:: R)? := e in e
-- >     | case r of (C [(x,bool)]* |-> (e | unreachable))*
-- >     | e ? (e proves r)
data Expr
  = -- | Refinement used as expression
    Reft Reft
  | -- | Let with type annotation. binds the dependent variables in R
    --   for lets in the code, we can always get an annotation, but we also create some for ANF
    Let Id (Maybe RefType) Expr Expr
  | -- | Pattern matching (includes conditionals), with Maybe for optional branches.
    --   The boolean in the list of parameters is true if the parameter is inductive
    --   and we are destructing one of the parameters of the function
    --   The last element indicates if the case must be translated to
    --   destruct (Nothing) or induction, in which case we have the list of variables to generalize
    Case Reft [((Id, [(Id, Bool)]), Maybe Expr)] (Maybe [Id])
  | QMark Expr Expr Reft
  deriving (Data, Show, Generic, Binary)

-- | Simple LH terms including formulas.
--   Terms of this type can occur as (sub)terms in refinements
--   Variables are annotated with their localization and,
--   if they are a function type, with their unrefined return type
--
-- > r ::= x/(A,loc)
-- >     | lit ∈ B
-- >     | C
-- >     | r r
-- >     | ¬r
-- >     | r `op` r
-- >     | r `pop` r
data Reft
  = Var Id (Maybe BaseType) Localization
  | StringLit String
  | IntLit Integer
  | FloatLit Double
  | DC Id
  | App Reft Reft
  | Neg Reft
  | Bop Bop Reft Reft
  | Pop ProofOp Reft Reft
  | Sub Reft RefType RefType
  | Inj Reft RefType
  | Proj ProjKind Reft
  deriving (Data, Eq, Show, Generic, Binary)

-- | The different kinds of projections:
-- `proj` from the generalized projections typeclass,
-- Rocq's `proj1_sig1` and `proj2_sig`
-- FIX: we shouldn't need this here, only in Rocq,
-- but Rocq cannot always find the correct instance
data ProjKind = GenProj | Sig1 | Sig2 deriving (Data, Eq, Show, Generic, Binary)

-- | Localization of the variables.
-- The recursive variables take the name of the induction variable
-- (this is used to clean up unused IHs) and the current branch pattern
--
-- loc ::= L | G | Y (x, σ)
data Localization = Local | Global | Recursive Id [DesState] deriving (Data, Eq, Show, Generic, Binary)

-- | State of the parameters: either intact (with name and arity) or destructed
-- This state is used to elaborate pattern matching and recursive variables, and to translate recursive calls
data DesState = Param Id Integer | Destructed deriving (Data, Eq, Show, Generic, Binary)

-- | Builtin binary operators (@op@)
data Bop
  = Plus
  | Minus
  | Times
  | Div
  | Mod
  | Eq
  | Neq
  | Leq
  | Geq
  | Lt
  | Gt
  | And
  | Or
  | Impl
  | Iff
  deriving (Data, Eq, Generic, Binary)

-- | Binary proof operators
--
-- > pop ::= === | =<= | =>=
data ProofOp = PEq | PLeq | PGeq deriving (Data, Eq, Generic, Binary)

-- Builtin type and data constructors

boolTp, unitTp :: BaseType
unitTm, ttTm, ffTm :: Reft
boolTp = TC boolTpName
unitTp = TC unitTpName

ttTm = DC ttTmName

ffTm = DC ffTmName

unitTm = DC unitTmName

-- * Functions on the terms

-- ** Constructions

-- | Make a local variable reference with a dummy type
mkVar :: Id -> Reft
mkVar x = Var x Nothing Local

-- ** Other functions

-- | arrs(R) := (x_i:R_i)_{i ≤ n} -> R' where n is maximal
arrs :: RefType -> ([(Id, RefType)], (Id, BaseType, Reft))
arrs (RefType x a r) = ([], (x, a, r))
arrs (ArrType x tpx tp) = ((x, tpx) :) `first` arrs tp

-- | Flattens an application
apps :: Reft -> (Reft, [Reft])
apps (App tm1 tm2) = let (hd, args) = apps tm1 in (hd, args ++ [tm2])
apps tm = (tm, [])

-- | Rename all the arguments of an arrow:
--
-- > renameParams([y1,y2], x1:{x1:B | True} -> x2:{x2:B | x1 == x2} -> {v:B | v = x1 + x2})
-- >   = y1:{x1:B | True} -> y2:{x2:B | y1 == x2} -> {v:B | v = y1 + y2}
renameParams :: [Id] -> RefType -> RefType
renameParams = aux []
  where
    aux :: [(Id, Id)] -> [Id] -> RefType -> RefType
    aux σ _ tp@(RefType {}) = renames σ tp
    aux σ [] tp = renames σ tp
    aux σ (y : ys) (ArrType x tpx tp)
      | x `notElem` freeVars tp || x == y =
          ArrType y (renames σ tpx) (aux σ ys tp)
    -- NOTE: we could handle some of the error cases by applying the
    -- substitutions globally for each binder, or by traversing the type in the
    -- opposite direction. But with reasonable namings that should not be necessary
    aux _ (y : _) tp0@(ArrType x _ tp)
      | y `elem` freeVars tp =
          error . render $ "Name clash while renaming variable" <+> text x <+> "to" <+> text y <+> "in" <+> pPrint tp0
    aux σ (y : ys) (ArrType x tpx tp) =
      ArrType y (renames σ tpx) (aux ((y, x) : σ) ys tp)

-- * Typeclass related to free variables

class HasVars a where
  -- | Return the free variables with their return type and localization
  freeVarsAnnot :: a -> Map Id (Maybe BaseType, Localization)

  -- | Return the bound variables with their type (they are all local)
  boundVars :: a -> Set Id

  -- | subst r x tm is {r/x}tm
  subst :: Reft -> Id -> a -> a

freeVars :: (HasVars a) => a -> Set Id
freeVars tm = Map.keysSet $ freeVarsAnnot tm

-- | return a variable fresh wrt to the free and bound variables in the second argument
fresh :: (HasVars a) => Id -> a -> Id
fresh x tm = freshVar x (freeVars tm `Set.union` boundVars tm)

-- | Rename the second argument to the first in the third
--
-- > rename y x tm = {y/x}tm
rename :: (HasVars a) => Id -> Id -> a -> a
rename new old tm =
  maybe
    tm
    (\(tp, loc) -> subst (Var new tp loc) old tm)
    (Map.lookup old $ freeVarsAnnot tm)

-- | Apply a list of renamings, starting from the right
renames :: (HasVars a) => [(Id, Id)] -> a -> a
renames = flip (foldr (uncurry rename))

-- | Apply a list of substitutions, starting from the right
substs :: (HasVars a) => [(Reft, Id)] -> a -> a
substs = flip (foldr (uncurry subst))

instance HasVars Reft where
  freeVarsAnnot (Var x tp loc) = Map.singleton x (tp, loc)
  freeVarsAnnot (App hd arg) = freeVarsAnnot [hd, arg]
  freeVarsAnnot (Bop _ r1 r2) = freeVarsAnnot [r1, r2]
  freeVarsAnnot (Neg r) = freeVarsAnnot r
  freeVarsAnnot (StringLit _; IntLit _; FloatLit _; DC _) = Map.empty
  freeVarsAnnot (Pop _ r1 r2) = freeVarsAnnot [r1, r2]
  freeVarsAnnot (Sub r from to) = freeVarsAnnot r `Map.union` freeVarsAnnot [from, to]
  freeVarsAnnot (Inj r tp) = freeVarsAnnot r `Map.union` freeVarsAnnot tp
  freeVarsAnnot (Proj _ r) = freeVarsAnnot r

  -- Empty on unelaborated refinements, but has the bound variables of the types in casts
  boundVars (Var {}; StringLit _; IntLit _; FloatLit _; DC _) = Set.empty
  boundVars (App hd arg) = boundVars [hd, arg]
  boundVars (Bop _ r1 r2) = boundVars [r1, r2]
  boundVars (Neg r) = boundVars r
  boundVars (Pop _ r1 r2) = boundVars [r1, r2]
  boundVars (Sub r from to) = boundVars r `Set.union` boundVars [from, to]
  boundVars (Inj r tp) = boundVars r `Set.union` boundVars tp
  boundVars (Proj _ r) = boundVars r

  subst r' x (Var y _ _) | y == x = r'
  subst _ _ r0@(Var {}; StringLit _; IntLit _; FloatLit _; DC _) = r0
  subst r' x (App h arg) = App (subst r' x h) (subst r' x arg)
  subst r' x (Bop bop r1 r2) = Bop bop (subst r' x r1) (subst r' x r2)
  subst r' x (Neg r) = Neg $ subst r' x r
  subst r' x (Pop pop r1 r2) = Pop pop (subst r' x r1) (subst r' x r2)
  subst r' x (Sub r tps tpt) = Sub (subst r' x r) (subst r' x tps) (subst r' x tpt)
  subst r' x (Inj r tp) = Inj (subst r' x r) (subst r' x tp)
  subst r' x (Proj kind r) = Proj kind (subst r' x r)

instance HasVars Expr where
  freeVarsAnnot (Reft r) = freeVarsAnnot r
  freeVarsAnnot (Let x tp ex e) =
    freeVarsAnnot tp `Map.union` Map.delete x (freeVarsAnnot [ex, e])
  freeVarsAnnot (Case r branches _) =
    freeVarsAnnot r `Map.union` Map.unions (map fvBranch branches)
    where
      fvBranch ((_, ys), ebr) = freeVarsAnnot ebr `Map.withoutKeys` Set.fromList (map fst ys)
  freeVarsAnnot (QMark r rh rp) = freeVarsAnnot [r, rh, Reft rp]

  boundVars (Reft r) = boundVars r
  boundVars (Let x tp ex e) =
    Set.singleton x `Set.union` boundVars tp `Set.union` boundVars [ex, e]
  boundVars (Case r branches _) =
    boundVars r `Set.union` Set.unions (map bvBranch branches)
    where
      bvBranch ((_, ys), e) = Set.fromList (map fst ys) `Set.union` boundVars e
  boundVars (QMark r rh rp) = boundVars [r, rh, Reft rp]

  subst r x (Reft re) = Reft $ subst r x re
  subst r x (Let y tp ey e')
    | y == x = Let y (subst r x tp) (subst r x ey) e'
    | y `Set.member` freeVars r && x `Set.member` freeVars e' =
        Let z (subst r x tp) (subst r x ey) (subst r x $ rename z y e')
    | otherwise = Let y (subst r x tp) (subst r x ey) (subst r x e')
    where
      z = freshVar y (freeVars r `Set.union` freeVars (Let y tp ey e'))
  subst r x (Case r' branches genVars) =
    Case (subst r x r') (map substBranch branches) genVars
    where
      substBranch br@((_, ys), ebr)
        | x `elem` map fst ys || maybe True (notElem x . freeVars) ebr = br
      substBranch ((c, ys), ebr) = ((c, ys'), subst r x $ renames α ebr)
        where
          freshYs = foldr freshVars [] ys
          α = filter (uncurry (/=)) $ zipWith (\(y, _) z -> (z, y)) ys freshYs
          ys' = zipWith (\(_, b) z -> (z, b)) ys freshYs
          freshVars (y, _) vars =
            if y `elem` freeVars r
              then freshVar y (fvre `Set.union` Set.fromList vars) : vars
              else y : vars
          fvre = freeVars r `Set.union` freeVars (Case r' branches genVars)
  subst r x (QMark r' rh rp) = QMark (subst r x r') (subst r x rh) (subst r x rp)

instance HasVars RefType where
  freeVarsAnnot (RefType x _ r) = Map.delete x (freeVarsAnnot r)
  freeVarsAnnot (ArrType x tpx tp) =
    freeVarsAnnot tpx `Map.union` Map.delete x (freeVarsAnnot tp)

  boundVars (RefType x _ r) = Set.singleton x `Set.union` boundVars r
  boundVars (ArrType x tpx tp) = Set.singleton x `Set.union` boundVars [tpx, tp]

  subst _ x tp@(RefType y _ _) | y == x = tp
  subst r x (RefType y b reft) = RefType y b $ subst r x reft
  subst r x (ArrType y tpy tp')
    | y == x = ArrType y (subst r x tpy) tp'
    | y `Set.member` freeVars r && x `Set.member` freeVars tp' =
        ArrType z (subst r x tpy) (subst r x $ rename z y tp')
    | otherwise = ArrType y (subst r x tpy) (subst r x tp')
    where
      z = freshVar y (freeVars r `Set.union` freeVars (ArrType y tpy tp'))

instance (HasVars a) => HasVars [a] where
  freeVarsAnnot tms = Map.unions $ map freeVarsAnnot tms
  boundVars tms = Set.unions $ map boundVars tms
  subst r x = fmap (subst r x)

instance (HasVars a) => HasVars (Maybe a) where
  freeVarsAnnot = maybe Map.empty freeVarsAnnot
  boundVars = maybe Set.empty boundVars
  subst r x = fmap (subst r x)

-- * Equality instance using α-renaming

instance Eq RefType where
  tp1@(RefType x tpx rx) == tp2@(RefType y tpy ry) =
    let z = fresh x [tp1, tp2]
        (α1, α2) = if x /= y then ([(z, x)], [(z, y)]) else ([], [])
     in tpx == tpy && renames α1 rx == renames α2 ry
  tp1@(ArrType x tpx tp1') == tp2@(ArrType y tpy tp2') =
    let z = fresh x [tp1, tp2]
        (α1, α2) = if x /= y then ([(z, x)], [(z, y)]) else ([], [])
     in tpx == tpy && renames α1 tp1' == renames α2 tp2'
  _ == _ = False

instance Eq Expr where
  Reft r1 == Reft r2 = r1 == r2
  e1@(Let x tpx ex e1') == e2@(Let y tpy ey e2') =
    let z = fresh x [e1, e2]
        (α1, α2) = if x /= y then ([(z, x)], [(z, y)]) else ([], [])
     in tpx == tpy && ex == ey && renames α1 e1' == renames α2 e2'
  e1@(Case r1 alts1 genVars1) == e2@(Case r2 alts2 genVars2) =
    -- Equality is sensitive to the order of the alternatives
    r1 == r2 && all eqBranch (zip alts1 alts2) && genVars1 == genVars2
    where
      eqBranch (((c1, ys1), ebr1), ((c2, ys2), ebr2)) =
        let freshYs = foldr freshVars [] (zip ys1 ys2)
            α ys = filter (uncurry (/=)) $ zipWith (\(y, _) z -> (z, y)) ys freshYs
         in c1 == c2 && renames (α ys1) ebr1 == renames (α ys2) ebr2
      freshVars ((y1, _), (y2, _)) vars =
        if y1 /= y2
          then freshVar y1 (freeVars [e1, e2] `Set.union` Set.fromList vars) : vars
          else y1 : vars
  _ == _ = False

-- * Printer for the grammar

-- | Number of spaces in the indentation
identNb :: Int
identNb = 2

-- ** Precedence levels

-- TODO: harmonize with Rocq for simplicity

arrPrec :: Rational
arrPrec = 0

appPrec :: Rational
appPrec = 10

bopPrec :: Bop -> Rational
bopPrec Mod = 7
bopPrec Plus = 6
bopPrec Minus = 6
bopPrec Times = 7
bopPrec Div = 7
bopPrec Eq = 4
bopPrec Neq = 4
bopPrec Leq = 4
bopPrec Geq = 4
bopPrec Lt = 4
bopPrec Gt = 4
bopPrec And = 3
bopPrec Or = 2
bopPrec Impl = 1
bopPrec Iff = 1

popPrec :: ProofOp -> Rational
popPrec _ = 4

-- ** Instances

instance Pretty Builtin where
  pPrint = text . show

instance Pretty BaseType where
  pPrint (Builtin b) = pPrint b
  pPrint (TC tc) = text tc

instance Pretty RefType where
  pPrintPrec _ _ (RefType _ a r) | r == ttTm = braces $ pPrint a
  pPrintPrec _ _ (RefType _ a r) | a == unitTp = braces . braces $ pPrint r
  pPrintPrec _ _ (RefType x a r) =
    braces (text x <> colon <+> pPrint a <+> char '|' <+> pPrint r)
  pPrintPrec l p (ArrType x tpx tp) =
    maybeParens (p > arrPrec) $ sep [text x <> colon <+> pPrintPrec l (arrPrec + 1) tpx, "->" <+> pPrintPrec l arrPrec tp]

instance Pretty Decl where
  pPrint (Data tc constrs) =
    sep [ppTC, nest identNb . sep $ map (\dc -> char '|' <+> ppConstr dc) constrs]
    where
      ppTC = "data" <+> text tc <+> ":="
      ppConstr (c, tpc) = text c <+> "::" <+> pPrint tpc
  pPrint (Definition f tp e isRefl) =
    sep [ppRefl <+> ppF, nest identNb (pPrint e)]
    where
      ppRefl = if isRefl then "refl" else empty
      ppF = "def" <+> text f <+> "::" <+> pPrint tp <+> ":="
  pPrint (Import modName decls) =
    vcat $ ("import" <+> text modName) : map (nest identNb . pPrint) decls

instance Pretty Expr where
  pPrint (Reft r) = pPrint r
  pPrint (Let x tpx ex e) = sep [sep [ppLet, pPrint ex], nest 1 ("in" <+> pPrint e)]
    where
      ppLet = "let" <+> ppTp <+> ":="
      ppTp = case tpx of
        Nothing -> text x
        Just tp -> parens (text x <> colon <+> pPrint tp)
  pPrint (Case r alts genVars) =
    vcat $ (des <+> pPrint r <+> "of") : map ppAlt alts
    where
      des = case genVars of Nothing -> "destruct"; Just _ -> "induct"
      ppAlt (pat, e) = sep [char '|' <+> ppPat pat <+> "->", nest identNb $ maybe "undefined" pPrint e]
      ppPat (c, ys) = text c <+> hsep (map (text . fst) ys)
  pPrint (QMark r rh rp) =
    pPrint r <+> char '?' <+> parens (pPrint rh <+> "proves" <+> pPrint rp)

instance Pretty Reft where
  pPrintPrec _ _ (Var x _ _) = text x
  pPrintPrec _ _ (StringLit s) = quotes $ text s
  pPrintPrec _ _ (IntLit i) = integer i
  pPrintPrec _ _ (FloatLit f) = double f
  pPrintPrec _ _ (DC c) = text c
  pPrintPrec l p (App r1 r2) =
    maybeParens (p > appPrec) $ pPrintPrec l p r1 <+> pPrintPrec l (appPrec + 1) r2
  pPrintPrec l p (Neg r) =
    maybeParens (p > appPrec) $ "not" <+> pPrintPrec l (appPrec + 1) r
  pPrintPrec l p (Bop bop r1 r2) =
    maybeParens (p > bopPrec bop) $ pPrintPrec l (bopPrec bop) r1 <+> pPrint bop <+> pPrintPrec l (bopPrec bop) r2
  pPrintPrec l p (Pop pop r1 r2) =
    maybeParens (p > popPrec pop) $ pPrintPrec l (popPrec pop) r1 <+> pPrint pop <+> pPrintPrec l (popPrec pop) r2
  pPrintPrec _ p (Sub r from to) =
    maybeParens (p > appPrec) $ "sub" <+> parens (hsep $ punctuate comma (pPrint r : map pPrint [from, to]))
  pPrintPrec _ p (Inj r tp) =
    maybeParens (p > appPrec) $ "inj" <+> parens (pPrint r <> comma <+> pPrint tp)
  pPrintPrec l p (Proj _ r) =
    maybeParens (p > appPrec) $ "proj" <+> pPrintPrec l (appPrec + 1) r

instance Pretty Localization where
  pPrint Local = char 'L'
  pPrint Global = char 'G'
  pPrint (Recursive indVar _) = char 'Y' <+> text indVar

instance Show Bop where
  show Mod = "`mod`"
  show Plus = "+"
  show Minus = "-"
  show Times = "*"
  show Div = "/"
  show Eq = "=="
  show Neq = "/="
  show Leq = "<="
  show Geq = ">="
  show Lt = "<"
  show Gt = ">"
  show And = "&&"
  show Or = "||"
  show Impl = "=>"
  show Iff = "<=>"

instance Pretty Bop where
  pPrint = text . show

instance Show ProofOp where
  show PEq = "==="
  show PLeq = "=<="
  show PGeq = "=>="

instance Pretty ProofOp where
  pPrint = text . show
