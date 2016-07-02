{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}

module Soundness where

import Prelude hiding (Maybe(..))
import Proves


data Maybe a = Nothing | Just a
  deriving (Show, Eq)

{-@ data Maybe a =
      Nothing
     | Just {select_Just_1 :: a} @-}

{-@ measure is_Nothing @-}
is_Nothing Nothing = True
is_Nothing _       = False

{-@ measure is_Just @-}
is_Just (Just _) = True
is_Just _        = False

-- | Data Types

data Type =
    TBool
  | TFun { tFunArg :: Type, tFunRes :: Type }
  deriving (Eq, Show)

{-@
data Type [tsize] =
    TBool
  | TFun { tFunArg :: Type, tFunRes :: Type }
@-}


data Expr =
    EVar { eVarVal :: Int }
  | EApp { eAppArg :: Expr , eAppRes :: Expr }
  | EAbs { eAbsVar :: Int, eAbsType :: Type, eAbsBody :: Expr }
  | ETrue
  | EFalse
  | EIf  { eIfCond :: Expr, eIfTrue :: Expr, eIfFalse :: Expr }
  deriving (Eq, Show)

{-@
data Expr [esize] =
    EVar { select_EVar_1 :: Int }
  | EApp { select_EApp_1 :: Expr , select_EApp_2 :: Expr }
  | EAbs { select_EAbs_1 :: Int,   select_EAbs_2 :: Type, select_EAbs_3 :: Expr }
  | ETrue
  | EFalse
  | EIf  { select_EIf_1 :: Expr, select_EIf_2 :: Expr, select_EIf_3 :: Expr }

@-}


{-@ measure is_EVar @-}
is_EVar (EVar _) = True
is_EVar _        = False

{-@ measure is_EApp @-}
is_EApp (EApp _ _) = True
is_EApp _          = False

{-@ measure is_EAbs @-}
is_EAbs (EAbs _ _ _) = True
is_EAbs _            = False

{-@ measure is_ETrue @-}
is_ETrue ETrue = True
is_ETrue _     = False

{-@ measure is_EFalse @-}
is_EFalse EFalse = True
is_EFalse _      = False

{-@ measure is_EIf @-}
is_EIf (EIf _ _ _) = True
is_EIf _            = False

{-@ measure esize @-}

{-@ invariant {v:Expr | 0 <= esize v } @-}
-- | Auto generated invariants does not work,
-- | see https://github.com/ucsd-progsys/liquidhaskell/issues/723

esize :: Expr -> Int
esize ETrue         = 0
esize EFalse        = 0
esize (EVar _)      = 1
esize (EApp e1 e2)  = 1 + esize e1 + esize e2
esize (EAbs _ _ e)  = 1 + esize e
esize (EIf c e1 e2) = 1 + esize c + esize e1 + esize e2

-- | Operational Semantics
{-@ measure isValue @-}
isValue :: Expr -> Bool
isValue (EAbs _ _ _) = True
isValue ETrue        = True
isValue EFalse       = True
isValue _            = False

{-@ axiomatize subst @-}
{-@ subst :: Int -> Expr -> e:Expr -> Expr / [esize e] @-}
subst x ex (EVar y)     | x == y
  = ex
subst x ex (EAbs y t e) | x /= y
  = EAbs y t (subst x ex e)
subst x ex (EApp e1 e2)
  = EApp (subst x ex e1) (subst x ex e2)
subst x ex (EIf c e1 e2)
  = EIf (subst x ex c) (subst x ex e1) (subst x ex e2)
subst x ex e
  = e


{-@ axiomatize step @-}
step :: Expr -> Maybe Expr
step (EApp e1 e2)
  = if isValue e1 then
       if isValue e2 then
          case e1 of
            EAbs x _ ex -> Just (subst x ex e2)
            _           -> Nothing
       else
           case step e2 of
             Just e2' -> Just (EApp e1 e2')
             _        -> Nothing
    else case step e1 of
           Just e1' -> Just (EApp e1' e2)
           _        -> Nothing
step (EIf c e1 e2)
  = if isValue c then
      case c of
        ETrue  -> Just e1
        EFalse -> Just e2
        _      -> Nothing
    else case step c of
          Just c' -> Just (EIf c' e1 e2)
          Nothing -> Nothing
step _
  = Nothing


test1 = step (EApp (EAbs 0 TBool (EVar 0)) ETrue) == Just ETrue
test2 = step (EApp ETrue ETrue) == Nothing


-- | Type Checker

type Env = Int -> Maybe Type
{-@ axiomatize empty  @-}
empty :: Env
empty _ = Nothing

extend :: Env -> Int -> Type -> Env
extend γ x t x' = if x == x' then Just t else γ x'

{-@ measure typing :: Env -> Expr -> Maybe Type @-}
typing :: Env -> Expr -> Maybe Type
typing γ (EVar x)
  = γ x
typing γ (EAbs x tx e)
  = case typing (extend γ x tx) e of
      Just t  -> Just $ TFun tx t
      Nothing -> Nothing
typing _ ETrue
  = Just TBool
typing _ EFalse
  = Just TBool
typing γ (EIf c e1 e2)
  = case (typing γ c, typing γ e1, typing γ e2) of
      (Just TBool, Just t1, Just t2) -> if t1 == t2 then Just t1 else Nothing
      _                              -> Nothing
typing γ (EApp e1 e2)
  = case (typing γ e1, typing γ e2) of
      (Just (TFun t11 t12), Just t2) -> if t11 == t2 then Just t12 else Nothing
      _                              -> Nothing



bar :: Eq b =>  Maybe b -> Proof
{-@ bar :: m:Maybe b -> {m == Nothing => not (is_Just m) } @-}
bar Nothing
  = is_Just Nothing ==! False ==! not True *** QED
bar (Just x) = simpleProof

foo :: Int -> Proof
{-@ foo :: v:Int -> { not (is_Just (typing empty (EVar v))) } @-}
foo v
  =   is_Just (typing empty (EVar v))
  ==! is_Just (empty v)
  ==! is_Just ((\_-> Nothing) v)
  ==! is_Just Nothing          ? bar (typing empty (EVar v))
  *** QED

-- | Soundness proofs
progress :: Expr -> Proof
{-@ progress :: e:{Expr | is_Just (typing empty e)}
             -> {isValue e || is_Just (step e)}
  @-}

progress (EVar x)
  = foo x
{-
typing γ (EAbs x tx e)
  = case typing (extend γ x tx) e of
      Just t  -> Just $ TFun tx t
      Nothing -> Nothing
typing _ ETrue
  = Just TBool
typing _ EFalse
  = Just TBool
typing γ (EIf c e1 e2)
  = case (typing γ c, typing γ e1, typing γ e2) of
      (Just TBool, Just t1, Just t2) -> if t1 == t2 then Just t1 else Nothing
      _                              -> Nothing
typing γ (EApp e1 e2)
  = case (typing γ e1, typing γ e2) of
      (Just (TFun t11 t12), Just t2) -> if t11 == t2 then Just t12 else Nothing
      _                              -> Nothing
-}
progress e
   = undefined
