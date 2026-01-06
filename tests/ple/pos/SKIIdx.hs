{-# Language GADTs, TypeFamilies, DataKinds #-}

{-@ LIQUID "--reflection"        @-}
{-@ LIQUID "--ple"               @-}
{-@ LIQUID "--etabeta"           @-}
{-@ LIQUID "--dependantcase"     @-}

module SKIIdx where

import Prelude

import Language.Haskell.Liquid.ProofCombinators

{-@ assume reflect id as myId @-}

{-@ reflect myId @-}
myId :: a -> a
myId x = x

data List a = Nil | Cons a (List a)
  deriving (Show)

data Ty
  = Iota
  | Arrow Ty Ty
  deriving Eq

type Ctx = List Ty

data Ref where
  {-@ Here :: σ:Ty -> γ:Ctx -> Ix Ref (σ, (Cons σ γ)) @-}
  Here :: Ty -> Ctx -> Ref

  {-@ There :: τ:Ty -> σ:Ty -> γ:Ctx -> Ix Ref (σ, γ)
            -> Ix Ref (σ, (Cons τ γ)) @-}
  There :: Ty -> Ty -> Ctx -> Ref -> Ref

data Term where
  {-@ App :: σ:Ty -> τ:Ty -> γ:Ctx -> Ix Term (γ, (Arrow σ τ))
          -> Ix Term (γ, σ) -> Ix Term (γ, τ) @-}
  App :: Ty -> Ty -> Ctx -> Term -> Term -> Term
  {-@ Lam :: σ:Ty -> τ:Ty -> γ:Ctx -> Ix Term ((Cons σ γ), τ)
          -> Ix Term (γ, (Arrow σ τ)) @-}
  Lam :: Ty -> Ty -> Ctx -> Term -> Term
  {-@ Var :: σ:Ty -> γ:Ctx -> Ix Ref (σ, γ) -> Ix Term (γ, σ) @-}
  Var :: Ty -> Ctx -> Ref -> Term

{-@ stratified Value @-}
data Value where
  {-@ VIota :: Int -> Ix Value Iota @-}
  VIota :: Int -> Value
  {-@ VFun :: σ:Ty -> τ:Ty -> (Ix Value σ -> Ix Value τ)
           -> Ix Value (Arrow σ τ) @-}
  VFun :: Ty -> Ty -> (Value -> Value) -> Value

data Env where
  {-@ Empty :: Ix Env Nil @-}
  Empty :: Env
  {-@ With :: σ:Ty -> γ:Ctx -> Ix Value σ -> Ix Env γ
           -> Ix Env (Cons σ γ) @-}
  With  :: Ty -> Ctx -> Value -> Env -> Env

{-@ reflect lookupRef @-}
{-@ lookupRef :: σ:Ty -> γ:Ctx -> r:Ix Ref (σ, γ) -> Ix Env γ
              -> Ix Value σ @-}
lookupRef :: Ty -> Ctx -> Ref -> Env -> Value
lookupRef _ _           (Here _ _)          (With _ _ a _)  = a
lookupRef σ (Cons γ γs) (There _ _ _ there) (With _ _ _ as) =
  lookupRef σ γs there as

{-@ reflect eval @-}
{-@ eval :: σ:Ty -> γ:Ctx -> t:Ix Term (γ, σ) -> Ix Env γ
         -> Ix Value σ @-}
eval :: Ty -> Ctx -> Term -> Env -> Value
eval σ           γ (App α _ _ t₁ t₂) e = case eval (Arrow α σ) γ t₁ e of
    VFun _ _ f -> f (eval α γ t₂ e)
eval σ           γ (Var _ _ x)       e = lookupRef σ γ x e
eval (Arrow α σ) γ (Lam _ _ _ t)     e = VFun α σ (\y -> eval σ (Cons α γ) t (With α γ y e))

{-@ reflect makeId @-}
{-@ makeId :: σ:Ty -> γ:Ctx -> (Ix Env γ -> Ix Value (Arrow σ σ)) @-}
makeId :: Ty -> Ctx -> (Env -> Value)
makeId σ γ v = VFun σ σ id

{-@ reflect makeApp @-}
{-@ makeApp :: σ:Ty -> τ:Ty -> γ:Ctx
            -> (Ix Env γ -> Ix Value (Arrow σ τ))
            -> (Ix Env γ -> Ix Value σ)
            -> Ix Env γ -> Ix Value τ @-}
makeApp :: Ty -> Ty -> Ctx -> (Env -> Value) -> (Env -> Value) -> Env -> Value
makeApp σ τ γ fun arg env = case fun env of
  VFun _ _ f -> f (arg env)

{-@ reflect makeConst @-}
{-@ makeConst :: σ:Ty -> τ:Ty -> γ:Ctx
              -> (Ix Env γ -> Ix Value (Arrow σ (Arrow τ σ))) @-}
makeConst :: Ty -> Ty -> Ctx -> (Env -> Value)
makeConst σ τ γ e = VFun σ (Arrow τ σ) $ \x -> VFun τ σ $ \y -> x


{-@ reflect makeS @-}
{-@ makeS :: σ:Ty -> τ:Ty -> υ:Ty -> γ:Ctx
          -> (Ix Env γ
             -> Ix Value (Arrow (Arrow σ (Arrow τ υ))
                                   (Arrow (Arrow σ τ) (Arrow σ υ))))@-}
makeS :: Ty -> Ty -> Ty -> Ctx -> (Env -> Value)
makeS σ τ υ γ e = VFun (Arrow σ (Arrow τ υ)) (Arrow (Arrow σ τ) (Arrow σ υ))
                    $ \(VFun _ _ x) -> VFun (Arrow σ τ) (Arrow σ υ) $ \(VFun _ _ y) -> VFun σ υ $ \z -> case (x z)
                        of VFun _ _ xz -> xz (y z)


{-@ reflect sType @-}
sType σ τ υ = Arrow (Arrow σ (Arrow τ υ)) (Arrow (Arrow σ τ) (Arrow σ υ))

{-@ reflect kType @-}
kType σ τ = Arrow σ (Arrow τ σ)

{-@ reflect iType @-}
iType σ = Arrow σ σ

{-@ reflect dom @-}
{-@ dom :: { σ:Ty | σ /= Iota } -> Ty @-}
dom (Arrow σ τ) = σ

{-@ reflect cod @-}
{-@ cod :: { σ:Ty | σ /= Iota } -> Ty @-}
cod (Arrow σ τ) = τ


data Comb where
  {-@ S :: σ:Ty -> τ:Ty -> υ:Ty -> γ:Ctx
        -> Ix Comb (γ, sType σ τ υ, makeS σ τ υ γ) @-}
  S :: Ty -> Ty -> Ty -> Ctx -> Comb
  {-@ K :: σ:Ty -> τ:Ty -> γ:Ctx
        -> Ix Comb (γ, kType σ τ, makeConst σ τ γ) @-}
  K :: Ty -> Ty -> Ctx -> Comb
  {-@ I :: σ:Ty -> γ:Ctx
        -> Ix Comb (γ, iType σ, makeId σ γ) @-}
  I :: Ty -> Ctx -> Comb
  {-@ CApp :: σ:Ty -> τ:Ty -> γ:Ctx
           -> fun:(Ix Env γ -> Ix Value (Arrow σ τ))
           -> arg:(Ix Env γ -> Ix Value σ)
           -> Ix Comb (γ, Arrow σ τ, fun)
           -> Ix Comb (γ, σ, arg)
           -> Ix Comb (γ, τ, makeApp σ τ γ fun arg) @-}
  CApp :: Ty -> Ty -> Ctx -> (Env -> Value) -> (Env -> Value) -> Comb -> Comb
       -> Comb
  {-@ CVar :: σ:Ty -> γ:Ctx -> r:Ix Ref (σ, γ)
           -> Ix Comb (γ, σ, lookupRef σ γ r) @-}
  CVar :: Ty -> Ctx -> Ref -> Comb

{-@ translate :: σ:Ty -> γ:Ctx -> t:Ix Term (γ, σ)
              -> Ix Comb (γ, σ, eval σ γ t)  @-}
translate :: Ty -> Ctx -> Term -> Comb
translate σ           γ (App α _ _ t₁ t₂) =
  CApp α σ γ (eval (Arrow α σ) γ t₁) (eval α γ t₂) t₁ₜ t₂ₜ
  where t₁ₜ = translate (Arrow α σ) γ t₁
        t₂ₜ = translate α           γ t₂
translate σ           γ (Var _ _ x)       =
  CVar σ γ x
translate (Arrow σ τ) γ (Lam _ _ _ t)     =
  bracket σ τ γ (eval τ (Cons σ γ) t) (translate τ (Cons σ γ) t)

{-@ reflect makeBracketing @-}
{-@ makeBracketing :: σ:Ty -> τ:Ty -> γ:Ctx
                   -> f:(Ix Env (Cons σ γ) -> Ix Value τ)
                   -> Ix Env γ
                   -> Ix Value (Arrow σ τ) @-}
makeBracketing :: Ty -> Ty -> Ctx -> (Env -> Value) -> Env -> Value
makeBracketing σ τ γ f env = VFun σ τ $ \x -> f (With σ γ x env)

{-@ bracket :: σ:Ty -> τ:Ty -> γ:Ctx -> f:(Ix Env (Cons σ γ) -> Ix Value τ)
            -> Ix Comb (Cons σ γ, τ, f)
            -> Ix Comb (γ, Arrow σ τ, makeBracketing σ τ γ f) @-}
bracket :: Ty -> Ty -> Ctx -> (Env -> Value) -> Comb -> Comb
bracket σ τ γ f (CApp α _ _ ft₁ ft₂ t₁ t₂)             =
  CApp (Arrow σ α) (Arrow σ τ) γ
       (makeApp (Arrow σ (Arrow α τ)) (Arrow (Arrow σ α) (Arrow σ τ))
                γ (makeS σ α τ γ) (makeBracketing σ (Arrow α τ) γ ft₁))
       (makeBracketing σ α γ ft₂) st t₂ᵣ
  where t₁ᵣ = bracket σ (Arrow α τ) γ ft₁ t₁
        t₂ᵣ = bracket σ α           γ ft₂ t₂
        st  = CApp (dom $ sType σ α τ) (cod $ sType σ α τ)
                   γ
                   (makeS σ α τ γ)
                   (makeBracketing σ (Arrow α τ) γ ft₁)
                   (S σ α τ γ) t₁ᵣ
bracket σ τ γ f (S τ₁ τ₂ τ₃ _)                 =
  CApp τ (Arrow σ τ) γ (makeConst τ σ γ) (makeS τ₁ τ₂ τ₃ γ)
       (K τ σ γ) (S τ₁ τ₂ τ₃ γ)
bracket σ τ γ f (K τ₁ τ₂ _)                    =
  CApp τ (Arrow σ τ) γ (makeConst τ σ γ) (makeConst τ₁ τ₂ γ)
       (K τ σ γ) (K τ₁ τ₂ γ)
bracket σ τ γ f (I τ₁ _)                       =
  CApp τ (Arrow σ τ) γ (makeConst τ σ γ) (makeId τ₁ γ)
       (K τ σ γ) (I τ₁ γ)
bracket σ τ γ f (CVar _ _ (Here _ _))          =
  I σ γ
bracket σ τ γ f (CVar _ _ (There _ _ _ there)) =
  CApp τ (Arrow σ τ) γ (makeConst τ σ γ) (lookupRef τ γ there)
       (K τ σ γ) (CVar τ γ there)
