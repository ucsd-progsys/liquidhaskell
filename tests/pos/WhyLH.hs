module WhyLH where

{-@ LIQUID "--ple" @-}
{-@ LIQUID "--exact-data-cons" @-}

-- This test contains the examples of the blogpost at
-- https://www.tweag.io/blog/2022-01-19-why-liquid-haskell/
--
import Language.Haskell.Liquid.ProofCombinators (pleUnfold)
import Prelude hiding (length, max)

{-@
type Nat = {i:Int | 0 <= i}

data UExp
  = UVar Nat
  | ULam Ty UExp
  | UApp { uapp1 :: UExp, uapp2 :: UExp }
 @-}
-- | Lambda expressions with types at the bindings.
data UExp
  = UVar Int
  | ULam Ty UExp
  | UApp { uapp1 :: UExp, uapp2 :: UExp }

-- | The types are the types of functions manipulating some opaque type @T@.
data Ty = T | TyFun Ty Ty
  deriving Eq

-- XXX: Using inline instead of reflect causes verification to fail
{-@ reflect max @-}
max :: Int -> Int -> Int
max a b = pleUnfold (if a > b then a else b)

-- XXX: using max causes verification to fail if not using
-- --ple-with-undecided-guards. Arguably, PLE should unfold max
-- since it is not doing pattern matching.
{-@
reflect freeVarBound
freeVarBound :: UExp -> Int
@-}
-- | Compute the lowest upper-bound of de Bruijn indices appearing
-- free in an expression.
freeVarBound :: UExp -> Int
freeVarBound (UVar v) = v + 1
freeVarBound (ULam _ body) = max (freeVarBound body - 1) 0
freeVarBound (UApp e1 e2) = max (freeVarBound e1) (freeVarBound e2)

{-@
type UExpN N = { e:UExp | freeVarBound e <= N }
type ClosedUExp = UExpN 0
@-}

{-@ exp0 :: ClosedUExp @-}
exp0 :: UExp
exp0 = ULam T (UVar 0)

{-@ exp1 :: UExpN 1 @-}
exp1 :: UExp
exp1 = UVar 0

{-@ exp2 :: ClosedUExp @-}
exp2 :: UExp
exp2 = ULam T (ULam T (UVar 0))

{-@ exp3 :: UExpN 1 @-}
exp3 :: UExp
exp3 = ULam T (ULam T (UVar 2))


{-@ reflect elemAt @-}
{-@ elemAt :: xs:[a] -> { i:Int | 0 <= i && i < length xs } -> a @-}
elemAt :: [a] -> Int -> a
elemAt (x:_) 0 = x
elemAt (_:xs) i = elemAt xs (i - 1)

{-@ reflect length @-}
length :: [a] -> Int
length [] = 0
length (_:xs) = 1 + length xs

{-@ reflect inferType @-}
{-@ inferType :: ctx:[Ty] -> UExpN (length ctx) -> Maybe Ty @-}
inferType :: [Ty] -> UExp -> Maybe Ty
inferType ctx (UVar i) = Just (elemAt ctx i)
inferType ctx (ULam t body) = case inferType (t:ctx) body of
  Just r -> Just (TyFun t r)
  Nothing -> Nothing
inferType ctx (UApp e0 e1) =
  pleUnfold  -- needed by uappArgT to avoid breaking the verification
             -- in all of these cases
    (case inferType ctx e0 of
      Just (TyFun a r) -> case inferType ctx e1 of
        Just t -> if a == t then Just r else Nothing
        Nothing -> Nothing
      _ -> Nothing
    )

{-@ type WellTypedExp CTX TY = { e:UExp | freeVarBound e <= length CTX && inferType CTX e == Just TY } @-}

{-@ reflect cons @-}
cons :: a -> [a] -> [a]
cons = (:)

{-@ exp4 :: WellTypedExp (cons T []) T @-}
exp4 :: UExp
exp4 = UVar 0

{-@ exp5 :: WellTypedExp [] (TyFun T T) @-}
exp5 :: UExp
exp5 = ULam T (UVar 0)

main :: IO ()
main = print ()

-- The following functions are an experiment on what LH can infer from
-- the arguments of a data constructor. Given a well-typed application
-- @UApp e0 e1@, can LH infer that @e0@ must have a function type and
-- that the type of @e1@ must match the argument type of @e0@.

{-@ uappArgT :: ctx:[Ty] -> e : { e:UExp | isUApp e && isJustTy (inferType ctx e) } -> { funTyM (inferType ctx (uapp2 e)) (inferType ctx e) == inferType ctx (uapp1 e) } @-}
uappArgT :: [Ty] -> UExp -> ()
uappArgT _ _ = ()

{-@ inline isUApp @-}
isUApp :: UExp -> Bool
isUApp (UApp _ _) = True
isUApp _ = False

-- Either inline or both reflect and pleUnfold are needed by `uappArgT`.
{-@ inline isJustTy @-}
isJustTy :: Maybe a -> Bool
isJustTy (Just _) = True
isJustTy _ = False

{-@ inline funTyM @-}
funTyM :: Maybe Ty -> Maybe Ty -> Maybe Ty
funTyM (Just a) (Just b) = Just (TyFun a b)
funTyM _ _ = Nothing
