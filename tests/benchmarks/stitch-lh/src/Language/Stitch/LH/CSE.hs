{-# LANGUAGE PolyKinds, GADTs, MultiParamTypeClasses, LambdaCase,
             TypeFamilies, TypeOperators, RankNTypes, AllowAmbiguousTypes,
             ScopedTypeVariables, TypeApplications, DataKinds #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Stitch.LH.CSE
-- Copyright   :  (C) 2018 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Richard Eisenberg (rae@richarde.dev)
-- Stability   :  experimental
--
-- Eliminate common sub-expressions from a Stitch program
--
----------------------------------------------------------------------------

module Language.Stitch.LH.CSE ( cse ) where

{- GENERAL APPROACH

We do CSE in three steps:

1. Recur through an expression. At every point in the AST with more than
   one subexpression (e.g., App, Cond, etc.), check to see if the same
   subsubexpression appears in more than subexpression. For example,
   App (... blah ...) (... blah ...). If so, add a new let-binding for
   the common subsubexpression. This is done by insertLets.

2. Recur through an expression. For every Let, remember the let-bound
   variable's RHS in a map. If that expression is seen, replace the expression
   with the let-bound variable. This is done by replaceExprs.

3. Recur through an expression. For every Let, do two things:
   a. If the RHS of the let-bound variable is just a variable, map the LHS to
      the RHS, applying the mapping to the body of the let.
   b. If the let-bound variable is not used in its body, remove the Let entirely.
   This is done in zapLets.

   This last step is important because step 1 inserts a new Let for every common
   subsubexpression, even if there is a larger subsubexpression to be commoned
   up. Zapping the lets removes the cruft that step 1 might insert. Step 1 also
   will insert a Let at every interior node where multiple subexpressions have
   a subsubexpression in common; if a subsubexpression appears in *three* places,
   then we'll get two Lets, one at the top join and one at the lower join. (Indeed,
   this duplication of Lets is why we need part (a) of step 3.)
-}

import Language.Stitch.LH.Type
import Language.Stitch.LH.Exp
import Language.Stitch.LH.Shift
import Language.Stitch.LH.Util

import Language.Stitch.LH.Data.Vec
import Language.Stitch.LH.Data.Exists

import Data.Type.Equality

import qualified Language.Stitch.LH.Data.IHashMap.Lazy as M
import qualified Language.Stitch.LH.Data.IHashSet as S
import Language.Stitch.LH.Data.IHashable

import Data.Kind

-- | Perform common-subexpression elimination (CSE)
cse :: KnownLength ctx => Exp ctx ty -> Exp ctx ty
cse = zapLets . replaceExprs . insertLets

---------------------------------------------------------------------
-- The main types for the data structures used in this file

-- | A mapping from expressions in a certain context to a type indexed
-- by the type of expression it is stored with
type ExpMap ctx a = M.IHashMap (Exp ctx) a

-- | A set of expressions in a certain context
type ExpSet ctx   = S.IHashSet (Exp ctx)

---------------------------------------------------------------------
-- Step 1. insertLets

-- | Implements Step 1 from the general description of CSE, above
insertLets :: KnownLength ctx => Exp ctx ty -> Exp ctx ty
insertLets = fst . go
  where
    go :: forall ctx ty. KnownLength ctx => Exp ctx ty -> (Exp ctx ty, ExpSet ctx)
    go e@(Var {}) = (e, S.empty)
    go (Lam arg_ty e1)
      = let (e1', all_exprs) = go e1
            e' = Lam arg_ty e1' in
        mk_result e' [unshiftSet all_exprs]

    go (App e1 e2)
      = let (e1', all_exprs1) = go e1
            (e2', all_exprs2) = go e2
            e' = App e1' e2' in
        mk_result e' [all_exprs1, all_exprs2]

    go (Let e1 e2)
      = let (e1', all_exprs1) = go e1
            (e2', all_exprs2) = go e2
            e' = Let e1' e2'

            all_exprs2' = unshiftSet all_exprs2 in
        mk_result e' [all_exprs1, all_exprs2']

    go (Arith e1 op e2)
      = let (e1', all_exprs1) = go e1
            (e2', all_exprs2) = go e2
            e' = Arith e1' op e2' in
        mk_result e' [all_exprs1, all_exprs2]

    go (Cond e1 e2 e3)
      = let (e1', all_exprs1) = go e1
            (e2', all_exprs2) = go e2
            (e3', all_exprs3) = go e3
            e' = Cond e1' e2' e3' in
        mk_result e' [all_exprs1, all_exprs2, all_exprs3]

    go (Fix e1)
      = let (e1', all_exprs) = go e1
            e' = Fix e1' in
        mk_result e' [all_exprs]

    go e@(IntE {}) = (e, S.empty)
    go e@(BoolE {}) = (e, S.empty)

    mk_result :: KnownLength ctx => Exp ctx ty -> [ExpSet ctx] -> (Exp ctx ty, ExpSet ctx)
    mk_result e all_exprss
      = (mkLets common_exprs e, S.insert e all_exprs)
      where
        pairs = allPairs all_exprss
        inters = map (uncurry S.intersection) pairs
        common_exprs = S.toList (S.unions inters)
        all_exprs = S.unions all_exprss

-- | A 'ShiftedExp' represents an expression that's been shifted into a deeper
-- context. Note the non-prenex kind, necessary so that Lets can be parameterized
-- by a partial application of this type.
newtype ShiftedExp base_ctx :: forall n. Ctx n -> Ty -> Type where
  ShiftedExp :: Exp (prefix +++ base_ctx) ty
             -> ShiftedExp base_ctx prefix ty

-- | A snoc-list (the "nil" is at the left) of expressions, where later elements
-- are in a deeper context than earlier ones.
data Lets :: forall n. (forall m. Ctx m -> Ty -> Type) -> Ctx n -> Type where
  LNil  :: forall (a :: forall m. Ctx m -> Ty -> Type). Lets a VNil
  (:<:) :: forall (a :: forall m. Ctx m -> Ty -> Type) ctx ty.
           Lets a ctx -> a ctx ty -> Lets a (ty :> ctx)
infixl 5 :<:

-- | Convert a list of expressions (of a variety of types) into a 'Lets' construct,
-- in CPS-style.
expsToLets :: [Ex (Exp ctx)]
           -> (forall n (prefix :: Ctx n). Lets (ShiftedExp ctx) prefix -> Length prefix -> r)
           -> r
expsToLets []              k = k LNil LZ
expsToLets (Ex exp : rest) k = expsToLets rest $ \ lets len ->
                               k (lets :<: ShiftedExp (shifts len exp)) (LS len)

-- | Wrap an expression in nested Lets. This version is efficient, shifting expressions
-- by many levels at once.
mkLets :: forall ctx ty. [Ex (Exp ctx)] -> Exp ctx ty -> Exp ctx ty
mkLets exps body = expsToLets exps $ \ lets len -> go lets (shifts len body)
  where
    go :: forall n (prefix :: Ctx n) ty.
          Lets (ShiftedExp ctx) prefix -> Exp (prefix +++ ctx) ty -> Exp ctx ty
    go LNil                      body = body
    go (rest :<: ShiftedExp exp) body = go rest (Let exp body)

-- | Wrap an expression in nested Lets. This version is very inefficient, doing
-- lots of single shifts.
_mkLetsSimple :: forall ctx ty. [Ex (Exp ctx)] -> Exp ctx ty -> Exp ctx ty
_mkLetsSimple []              body = body
_mkLetsSimple (Ex exp : rest) body = Let exp (shift (_mkLetsSimple rest body))

---------------------------------------------------------------------
-- Step 2. replaceExprs

-- | Implements Step 2 from the general description of CSE, above
replaceExprs :: KnownLength ctx => Exp ctx ty -> Exp ctx ty
replaceExprs = go M.empty
  where
    go :: forall n (ctx :: Ctx n) ty.
          KnownLength ctx => ExpMap ctx (Elem ctx) -> Exp ctx ty -> Exp ctx ty
    go m e
      | Just v <- M.lookup e m
      = Var v

    go m (Let e1 e2)
      = let e1' = go m e1
            m' = add_mapping (shift e1) $ add_mapping (shift e1') (shiftMap m) in
        Let e1' (go m' e2)

    go _ e@(Var {}) = e
    go m (Lam arg_ty e) = Lam arg_ty (go (shiftMap m) e)
    go m (App e1 e2) = App (go m e1) (go m e2)
    go m (Arith e1 op e2) = Arith (go m e1) op (go m e2)
    go m (Cond e1 e2 e3) = Cond (go m e1) (go m e2) (go m e3)
    go m (Fix e) = Fix (go m e)
    go _ e@(IntE {}) = e
    go _ e@(BoolE {}) = e

    add_mapping e m = insertIfAbsent e EZ m

insertIfAbsent :: (TestEquality k, IHashable k)
               => k i -> v i -> M.IHashMap k v -> M.IHashMap k v
insertIfAbsent k v m = M.alter (\case Just v0 -> Just v0
                                      Nothing -> Just v)
                               k m
---------------------------------------------------------------------
-- Step 3. zapLets

-- | Implements Step 3 from the general description of CSE, above
zapLets :: KnownLength ctx => Exp ctx ty -> Exp ctx ty
zapLets = fst . go M.empty
  where
    go :: forall n (ctx :: Ctx n) ty.
          KnownLength ctx
       => M.IHashMap (Elem ctx) (Elem ctx)
       -> Exp ctx ty
       -> (Exp ctx ty, S.IHashSet (Elem ctx))

    go m (Let e1 e2)
      | Var v <- e1
      = let (e2', used_vars) = go (M.insert EZ (shift v) (shiftMap m)) e2
            e2''             = uncheckedUnshift e2' in
        (e2'', unshiftSet used_vars)

      | otherwise
      = let (e1', used_vars1) = go m e1
            (e2', used_vars2) = go (shiftMap m) e2
            used_vars2' = unshiftSet used_vars2 in

        if S.member EZ used_vars2
        then (Let e1' e2', S.unions [used_vars1, used_vars2'])
        else (uncheckedUnshift e2', used_vars2')

    go m e@(Var v)
      | Just v' <- M.lookup v m
      = (Var v', S.singleton v')

      | otherwise
      = (e, S.singleton v)

    go m (Lam arg_ty e)
      = let (e', used_vars) = go (shiftMap m) e in
        (Lam arg_ty e', unshiftSet used_vars)

    go m (App e1 e2)
      = let (e1', used_vars1) = go m e1
            (e2', used_vars2) = go m e2 in
        (App e1' e2', used_vars1 `S.union` used_vars2)

    go m (Arith e1 op e2)
      = let (e1', used_vars1) = go m e1
            (e2', used_vars2) = go m e2 in
        (Arith e1' op e2', used_vars1 `S.union` used_vars2)

    go m (Cond e1 e2 e3)
      = let (e1', used_vars1) = go m e1
            (e2', used_vars2) = go m e2
            (e3', used_vars3) = go m e3 in
        (Cond e1' e2' e3', S.unions [used_vars1, used_vars2, used_vars3])

    go m (Fix e)
      = let (e', used_vars) = go m e in
        (Fix e', used_vars)

    go _ e@(IntE {})  = (e, S.empty)
    go _ e@(BoolE {}) = (e, S.empty)

---------------------------------------------------------
-- Shifting utilities

shiftMap :: forall (a :: forall n. Ctx n -> Ty -> Type)
                   (b :: forall n. Ctx n -> Ty -> Type)
                   ctx ty.
            ( IHashable (a (ty :> ctx)), TestEquality (a (ty :> ctx))
            , Shiftable a, Shiftable b )
         => M.IHashMap (a ctx) (b ctx) -> M.IHashMap (a (ty :> ctx)) (b (ty :> ctx))
shiftMap = M.foldrWithKey go M.empty
  where go exp el m = M.insert (shift exp) (shift el) m

unshiftSet :: forall (a :: forall n. Ctx n -> Ty -> Type) ty ctx.
              (Shiftable a, TestEquality (a ctx), IHashable (a ctx))
           => S.IHashSet (a (ty :> ctx))
           -> S.IHashSet (a ctx)
unshiftSet = S.foldr go S.empty
  where
    go exp set
      | Just exp' <- unshift exp
      = S.insert exp' set
      | otherwise
      = set

---------------------------------------------------------
-- Examples for testing

_testExp :: Exp VNil ((TInt :-> TInt) :-> TInt :-> TInt)
_testExp = Lam (SInt ::-> SInt) $
           Lam SInt $
           App (Lam SInt $
                App (Var (ES (ES EZ)))
                    (Var (ES EZ)))
               (App (Var (ES EZ))
                    (Var EZ))

_biggerExp :: Exp VNil ((TInt :-> TInt) :-> TInt :-> TInt)
_biggerExp = Lam (SInt ::-> SInt) $
             Lam SInt $
             App (Lam SInt $
                  App (Lam SInt $
                       App (Var (ES (ES (ES EZ))))
                           (Var (ES (ES EZ))))
                       (App (Var (ES (ES EZ)))
                            (Var (ES EZ))))
                 (App (Var (ES EZ))
                      (Var EZ))
