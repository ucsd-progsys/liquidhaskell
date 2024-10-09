{-# Language GADTs, TypeFamilies, DataKinds #-}

{-@ LIQUID "--reflection"                @-}
{-@ LIQUID "--ple"                       @-}
{-@ LIQUID "--max-case-expand=4"         @-}
{-@ LIQUID "--etabeta"                   @-}

module SKIEta where

import Prelude hiding (length, const, id)

import Language.Haskell.Liquid.ProofCombinators

data List a = Nil | Cons a (List a)
  deriving (Show)

data Ty
  = Iota
  | Arrow Ty Ty
  deriving Eq

type Ctx = List Ty

data Ref where
  {-@ Here :: σ:Ty -> γ:Ctx -> Prop (Ref σ (Cons σ γ)) @-}
  Here :: Ty -> Ctx -> Ref

  {-@ There :: τ:Ty -> σ:Ty -> γ:Ctx -> Prop (Ref σ γ) 
            -> Prop (Ref σ (Cons τ γ)) @-}
  There :: Ty -> Ty -> Ctx -> Ref -> Ref
data REF = Ref Ty Ctx

data Term where
  {-@ App :: σ:Ty -> τ:Ty -> γ:Ctx -> Prop (Term γ (Arrow σ τ)) 
          -> Prop (Term γ σ) -> Prop (Term γ τ) @-}
  App :: Ty -> Ty -> Ctx -> Term -> Term -> Term
  {-@ Lam :: σ:Ty -> τ:Ty -> γ:Ctx -> Prop (Term (Cons σ γ) τ) 
          -> Prop (Term γ (Arrow σ τ)) @-}
  Lam :: Ty -> Ty -> Ctx -> Term -> Term
  {-@ Var :: σ:Ty -> γ:Ctx -> Prop (Ref σ γ) -> Prop (Term γ σ) @-}
  Var :: Ty -> Ctx -> Ref -> Term
data TERM = Term Ctx Ty

{-@ measure tlen @-}
{-@ tlen :: Term -> Nat @-}
tlen :: Term -> Int
tlen (App _ _ _ t₁ t₂) = 1 + tlen t₁ + tlen t₂
tlen (Lam _ _ _ t)     = 1 + tlen t
tlen (Var _ _ _)       = 0


-- VFun function is non positive idk how to fix
{-@ LIQUID "--no-positivity-check" @-}
data Value where
  {-@ VIota :: Int -> Prop (Value Iota) @-}
  VIota :: Int -> Value
  {-@ VFun :: σ:Ty -> τ:Ty -> (Prop (Value σ) -> Prop (Value τ)) 
           -> Prop (Value (Arrow σ τ)) @-}
  VFun :: Ty -> Ty -> (Value -> Value) -> Value
data VALUE = Value Ty

{-@ reflect asFun @-}
{-@ asFun :: σ:Ty -> τ:Ty -> Prop (Value (Arrow σ τ)) 
          -> (Prop (Value σ) -> Prop (Value τ)) @-}
asFun :: Ty -> Ty -> Value -> (Value -> Value)
asFun _ _ (VFun _ _ fn) = fn

data Env where
  {-@ Empty :: Prop (Env Nil) @-}
  Empty :: Env
  {-@ With :: σ:Ty -> γ:Ctx -> Prop (Value σ) -> Prop (Env γ) 
           -> Prop (Env (Cons σ γ)) @-}
  With  :: Ty -> Ctx -> Value -> Env -> Env
data ENV = Env Ctx

{-@ reflect lookupRef @-}
{-@ lookupRef :: σ:Ty -> γ:Ctx -> r:Prop (Ref σ γ) -> Prop (Env γ) 
              -> Prop (Value σ) @-}
lookupRef :: Ty -> Ctx -> Ref -> Env -> Value
lookupRef _ _           (Here _ _)          (With _ _ a _)  = a
lookupRef σ (Cons γ γs) (There _ _ _ there) (With _ _ _ as) =
  lookupRef σ γs there as

{-@ makeFunBody :: σ:Ty -> α:Ty -> γ:Ctx -> t:Prop (Term (Cons α γ) σ) 
                -> Prop (Env γ) -> (Prop (Value α) -> Prop (Value σ))
                / [tlen t, 1] @-}
{-@ eval :: σ:Ty -> γ:Ctx -> t:Prop (Term γ σ) -> Prop (Env γ) 
         -> Prop (Value σ) / [tlen t, 0] @-}

{-@ reflect makeFunBody @-}
makeFunBody σ α γ t e x = eval σ (Cons α γ) t (With α γ x e)

{-@ reflect eval @-}
eval :: Ty -> Ctx -> Term -> Env -> Value
-- σ : ret type
-- γ : ctx
-- α : argtype
eval σ           γ (App α _ _ t₁ t₂) e = 
  (asFun α σ (eval (Arrow α σ) γ t₁ e)) (eval α γ t₂ e)
-- α : arg type
eval (Arrow α σ) γ (Lam _ _ _ t)     e = 
  VFun α σ (makeFunBody σ α γ t e)
  -- \x -> eval σ (Cons α γ) t (With α γ x e)
  -- where tₑ x = eval σ (Cons α γ) t (With α γ x e)
eval σ           γ (Var _ _ x)       e = 
  lookupRef σ γ x e

{-@ reflect id @-}
-- id :: Value -> Value
id :: a -> a
id a = a

{-@ reflect makeId @-}
{-@ makeId :: σ:Ty -> γ:Ctx -> (Prop (Env γ) -> Prop (Value (Arrow σ σ))) @-}
makeId :: Ty -> Ctx -> (Env -> Value)
makeId σ γ v = (VFun σ σ id)

{-@ reflect makeApp @-}
{-@ makeApp :: σ:Ty -> τ:Ty -> γ:Ctx 
            -> (Prop (Env γ) -> Prop (Value (Arrow σ τ)))
            -> (Prop (Env γ) -> Prop (Value σ))
            -> Prop (Env γ) -> Prop (Value τ) @-}
makeApp :: Ty -> Ty -> Ctx -> (Env -> Value) -> (Env -> Value) -> Env -> Value
makeApp σ τ γ fun arg env = asFun σ τ (fun env) (arg env)


{-@ reflect makeDiscard @-}
{-@ makeDiscard :: σ:Ty -> τ:Ty -> Prop (Value σ) 
                -> (Prop (Value τ) -> Prop (Value σ)) @-}
makeDiscard :: Ty -> Ty -> Value -> (Value -> Value)
makeDiscard σ τ x y = x

{-@ reflect makeConstIn @-}
{-@ makeConstIn :: σ:Ty -> τ:Ty 
                -> (Prop (Value σ) -> Prop (Value (Arrow τ σ))) @-}
makeConstIn :: Ty -> Ty -> (Value -> Value)
makeConstIn σ τ x = VFun τ σ (makeDiscard σ τ x)

{-@ reflect makeConst @-}
{-@ makeConst :: σ:Ty -> τ:Ty -> γ:Ctx 
              -> (Prop (Env γ) -> Prop (Value (Arrow σ (Arrow τ σ)))) @-}
makeConst :: Ty -> Ty -> Ctx -> (Env -> Value)
makeConst σ τ γ e = (VFun σ (Arrow τ σ) (makeConstIn σ τ))

{-@ reflect makeS1 @-}
{-@ makeS1 :: σ:Ty -> τ:Ty -> υ:Ty 
           -> (Prop (Value (Arrow σ (Arrow τ υ))) 
              -> Prop (Value (Arrow (Arrow σ τ) (Arrow σ υ)))) @-}
makeS1 :: Ty -> Ty -> Ty -> (Value -> Value)
makeS1 σ τ υ x = VFun (Arrow σ τ) (Arrow σ υ) (makeS2 σ τ υ x)

{-@ reflect makeS2 @-}
{-@ makeS2 :: σ:Ty -> τ:Ty -> υ:Ty -> Prop (Value (Arrow σ (Arrow τ υ)))
           -> (Prop (Value (Arrow σ τ)) -> Prop (Value (Arrow σ υ))) @-}
makeS2 :: Ty -> Ty -> Ty -> Value -> (Value -> Value)
makeS2 σ τ υ x y = VFun σ υ (makeS3 σ τ υ x y)

{-@ reflect makeS3 @-}
{-@ makeS3 :: σ:Ty -> τ:Ty -> υ:Ty -> Prop (Value (Arrow σ (Arrow τ υ)))
           -> Prop (Value (Arrow σ τ)) -> (Prop (Value σ) -> Prop (Value υ)) @-}
makeS3 :: Ty -> Ty -> Ty -> Value -> Value -> (Value -> Value)
makeS3 σ τ υ x y z = asFun τ υ (asFun σ (Arrow τ υ) x z) (asFun σ τ y z)

{-@ reflect makeS @-}
{-@ makeS :: σ:Ty -> τ:Ty -> υ:Ty -> γ:Ctx 
          -> (Prop (Env γ) 
             -> Prop (Value (Arrow (Arrow σ (Arrow τ υ)) 
                                   (Arrow (Arrow σ τ) (Arrow σ υ)))))@-}
makeS :: Ty -> Ty -> Ty -> Ctx -> (Env -> Value)
makeS σ τ υ γ e = (VFun (Arrow σ (Arrow τ υ)) 
                            (Arrow (Arrow σ τ) (Arrow σ υ)) 
                            (makeS1 σ τ υ))


{-@ reflect sType @-}
sType σ τ υ = Arrow (Arrow σ (Arrow τ υ)) (Arrow (Arrow σ τ) (Arrow σ υ))

{-@ reflect kType @-}
kType σ τ = Arrow σ (Arrow τ σ)

{-@ reflect iType @-}
iType σ = Arrow σ σ

data Comb where
  {-@ S :: σ:Ty -> τ:Ty -> υ:Ty -> γ:Ctx 
        -> Prop (Comb γ (sType σ τ υ) (makeS σ τ υ γ)) @-}
  S :: Ty -> Ty -> Ty -> Ctx -> Comb
  {-@ K :: σ:Ty -> τ:Ty -> γ:Ctx
        -> Prop (Comb γ (kType σ τ) (makeConst σ τ γ)) @-}
  K :: Ty -> Ty -> Ctx -> Comb
  {-@ I :: σ:Ty -> γ:Ctx 
        -> Prop (Comb γ (iType σ) (makeId σ γ)) @-}
  I :: Ty -> Ctx -> Comb
  {-@ CApp :: σ:Ty -> τ:Ty -> γ:Ctx 
           -> fun:(Prop (Env γ) -> Prop (Value (Arrow σ τ)))
           -> arg:(Prop (Env γ) -> Prop (Value σ))
           -> Prop (Comb γ (Arrow σ τ) fun)
           -> Prop (Comb γ σ arg) 
           -> Prop (Comb γ τ (makeApp σ τ γ fun arg)) @-}
  CApp :: Ty -> Ty -> Ctx -> (Env -> Value) -> (Env -> Value) -> Comb -> Comb 
       -> Comb
  {-@ CVar :: σ:Ty -> γ:Ctx -> r:Prop (Ref σ γ)
           -> Prop (Comb γ σ (lookupRef σ γ r)) @-}
  CVar :: Ty -> Ctx -> Ref -> Comb
data COMB = Comb Ctx Ty (Env -> Value)

{-@ translate :: σ:Ty -> γ:Ctx -> t:Prop (Term γ σ) 
              -> Prop (Comb γ σ (eval σ γ t))  @-}
translate :: Ty -> Ctx -> Term -> Comb
translate σ           γ (App α _ _ t₁ t₂) = 
  CApp α σ γ (eval (Arrow α σ) γ t₁) (eval α γ t₂) t₁ₜ t₂ₜ 
  where t₁ₜ = translate (Arrow α σ) γ t₁
        t₂ₜ = translate α           γ t₂
translate σ           γ (Var _ _ x)       = 
  CVar σ γ x 
translate (Arrow σ τ) γ (Lam _ _ _ t)     = 
  bracket σ τ γ (eval τ (Cons σ γ) t) (translate τ (Cons σ γ) t)

{-@ reflect makeBracketingInside @-}
{-@ makeBracketingInside :: σ:Ty -> τ:Ty -> γ:Ctx 
                         -> f:(Prop (Env (Cons σ γ)) -> Prop (Value τ))
                         -> Prop (Env γ)
                         -> Prop (Value σ)
                         -> Prop (Value τ) @-}
makeBracketingInside :: Ty -> Ty -> Ctx -> (Env -> Value) -> Env -> Value -> Value
makeBracketingInside σ τ γ f env x = f (With σ γ x env)

{-@ reflect makeBracketing @-}
{-@ makeBracketing :: σ:Ty -> τ:Ty -> γ:Ctx 
                   -> f:(Prop (Env (Cons σ γ)) -> Prop (Value τ))
                   -> Prop (Env γ)
                   -> Prop (Value (Arrow σ τ)) @-}
makeBracketing :: Ty -> Ty -> Ctx -> (Env -> Value) -> Env -> Value
makeBracketing σ τ γ f env = VFun σ τ (makeBracketingInside σ τ γ f env)

{-@ bracketHere :: σ:Ty -> γ:Ctx
                 -> {makeBracketing σ σ γ (lookupRef σ (Cons σ γ) (Here σ γ)) 
                     == makeId σ γ} @-}
bracketHere :: Ty -> Ctx -> Proof
bracketHere σ γ = trivial

{-@ bracketThere :: σ:Ty -> τ:Ty -> γ:Ctx -> t:Prop (Ref τ γ)
                 -> {makeBracketing σ τ γ (lookupRef τ (Cons σ γ) 
                                                       (There σ τ γ t))
                     == makeApp τ (Arrow σ τ) γ (makeConst τ σ γ) 
                                                (lookupRef τ γ t)} @-}
bracketThere :: Ty -> Ty -> Ctx -> Ref -> Proof
bracketThere σ τ γ t = trivial
 

{-@ bracketId :: σ:Ty -> τ:Ty -> γ:Ctx
               -> {makeBracketing σ (Arrow τ τ) γ (makeId τ (Cons σ γ))
                  = makeApp (Arrow τ τ) (Arrow σ (Arrow τ τ)) γ (makeConst (Arrow τ τ) σ γ) (makeId τ γ)} @-}
bracketId :: Ty -> Ty -> Ctx -> Proof
bracketId σ τ γ = trivial

{-@ bracketConst :: σ:Ty -> τ:Ty -> υ:Ty -> γ:Ctx
                -> {makeBracketing σ (kType τ υ) γ (makeConst τ υ (Cons σ γ))
                    = makeApp (kType τ υ) (Arrow σ (kType τ υ)) γ 
                              (makeConst (kType τ υ) σ γ) (makeConst τ υ γ)} @-}
bracketConst :: Ty -> Ty -> Ty -> Ctx -> Proof
bracketConst σ τ υ γ = trivial

{-@ bracketS :: σ:Ty -> τ:Ty -> υ:Ty -> ψ:Ty -> γ:Ctx
                -> {makeBracketing σ (sType τ υ ψ) γ (makeS τ υ ψ (Cons σ γ))
                    = makeApp (sType τ υ ψ) (Arrow σ (sType τ υ ψ)) γ 
                              (makeConst (sType τ υ ψ) σ γ) (makeS τ υ ψ γ)} @-}
bracketS :: Ty -> Ty -> Ty -> Ty -> Ctx -> Proof
bracketS σ τ υ ψ γ = trivial

{-@ bracketApp :: σ:Ty -> α:Ty -> τ:Ty -> γ:Ctx 
               -> ft1:(Prop (Env (Cons σ γ)) -> Prop (Value (Arrow α τ)))
               -> ft2:(Prop (Env (Cons σ γ)) -> Prop (Value α))
               -> {makeApp (Arrow σ α) (Arrow σ τ) γ 
                           (makeApp (Arrow σ (Arrow α τ)) 
                                    (Arrow (Arrow σ α) (Arrow σ τ)) γ 
                                    (makeS σ α τ γ) 
                                    (makeBracketing σ (Arrow α τ) γ ft1))
                           (makeBracketing σ α γ ft2)
                   == makeBracketing σ τ γ (makeApp α τ (Cons σ γ) ft1 ft2)} @-}
bracketApp :: Ty -> Ty -> Ty -> Ctx -> (Env -> Value) -> (Env -> Value) -> Proof
bracketApp σ α τ γ ft1 ft2 = trivial

{-@ bracket :: σ:Ty -> τ:Ty -> γ:Ctx -> f:(Prop (Env (Cons σ γ)) -> Prop (Value τ)) 
            -> Prop (Comb (Cons σ γ) τ f) 
            -> Prop (Comb γ (Arrow σ τ) (makeBracketing σ τ γ f)) @-}
bracket :: Ty -> Ty -> Ctx -> (Env -> Value) -> Comb -> Comb
bracket σ τ γ f (CApp α _ _ ft₁ ft₂ t₁ t₂)             =
  CApp (Arrow σ α) (Arrow σ τ) γ 
       (makeApp (Arrow σ (Arrow α τ)) (Arrow (Arrow σ α) (Arrow σ τ)) 
                γ (makeS σ α τ γ) (makeBracketing σ (Arrow α τ) γ ft₁))
       (makeBracketing σ α γ ft₂) st t₂ᵣ
       ? bracketApp σ α τ γ ft₁ ft₂
  where t₁ᵣ = bracket σ (Arrow α τ) γ ft₁ t₁
        t₂ᵣ = bracket σ α           γ ft₂ t₂
        st  = CApp (Arrow σ (Arrow α τ))
                   (Arrow (Arrow σ α) (Arrow σ τ))
                   γ
                   (makeS σ α τ γ)
                   (makeBracketing σ (Arrow α τ) γ ft₁)
                   (S σ α τ γ) t₁ᵣ
bracket σ τ γ f (S τ₁ τ₂ τ₃ _)                 =
  CApp τ (Arrow σ τ) γ (makeConst τ σ γ) (makeS τ₁ τ₂ τ₃ γ) 
       (K τ σ γ) (S τ₁ τ₂ τ₃ γ) 
       ? bracketS σ τ₁ τ₂ τ₃ γ
bracket σ τ γ f (K τ₁ τ₂ _)                    = 
  CApp τ (Arrow σ τ) γ (makeConst τ σ γ) (makeConst τ₁ τ₂ γ)
       (K τ σ γ) (K τ₁ τ₂ γ) 
       ? bracketConst σ τ₁ τ₂ γ
bracket σ τ γ f (I τ₁ _)                       =
  CApp τ (Arrow σ τ) γ (makeConst τ σ γ) (makeId τ₁ γ) 
       (K τ σ γ) (I τ₁ γ) 
       ? bracketId σ τ₁ γ
bracket σ τ γ f (CVar _ _ (Here _ _))          =
  I σ γ ? bracketHere σ γ
bracket σ τ γ f (CVar _ _ (There _ _ _ there)) = 
  CApp τ (Arrow σ τ) γ (makeConst τ σ γ) (lookupRef τ γ there) 
       (K τ σ γ) (CVar τ γ there) 
       ? bracketThere σ τ γ there