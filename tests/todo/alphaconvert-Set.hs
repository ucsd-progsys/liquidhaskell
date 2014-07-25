{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--fullcheck"      @-}

module AlphaConvert (subst) where

import qualified Data.Set as S

import Language.Haskell.Liquid.Prelude   

freshS  :: S.Set Bndr -> Bndr
alpha   :: S.Set Bndr -> Expr -> Expr 
subst   :: Expr -> Bndr -> Expr -> Expr
free    :: Expr -> S.Set Bndr


---------------------------------------------------------------------
-- | Datatype Definition --------------------------------------------
---------------------------------------------------------------------

type Bndr 
  = Int

data Expr 
  = Var Bndr  
  | Abs Bndr Expr
  | App Expr Expr

{-@ measure fv       :: Expr -> (S.Set Bndr)
    fv (Var x)       = (Set_sng x)
    fv (Abs x e)     = (Set_dif (fv e) (Set_sng x))
    fv (App e a)     = (Set_cup (fv e) (fv a)) 
  @-}

{-@ measure isAbs    :: Expr -> Prop
    isAbs (Var v)    = false
    isAbs (Abs v e)  = true
    isAbs (App e a)  = false             
  @-}

{-@ predicate Elem  X Ys       = Set_mem X Ys               @-}
{-@ predicate NotElem X Ys     = not (Elem X Ys)            @-}
{-@ predicate AddV E E2 X E1   = fv E = Set_cup (Set_dif (fv E2) (Set_sng X)) (fv E1) @-}
{-@ predicate EqV E1 E2        = fv E1 = fv E2                                        @-}
{-@ predicate Occ X E          = Set_mem X (fv E)                                     @-}
{-@ predicate Subst E E1 X E2  = if (Occ X E2) then (AddV E E2 X E1) else (EqV E E2)  @-}

----------------------------------------------------------------------------
-- | Part 5: Capture Avoiding Substitution ---------------------------------
----------------------------------------------------------------------------
{-@ subst :: e1:Expr -> x:Bndr -> e2:Expr -> {e:Expr | Subst e e1 x e2} @-} 
----------------------------------------------------------------------------

subst e' x e@(Var y)
  | x == y                = e' 
  | otherwise             = e

subst e' x (App ea eb)    = App ea' eb'
  where
    ea'                   = subst e' x ea
    eb'                   = subst e' x eb

subst e1 x e2@(Abs y e)   
  | x == y                = e2
  | y `S.member` xs       = subst e1 x (alpha xs e2) 
  | otherwise             = Abs y (subst e1 x e)
    where
      xs                  = free e1  

----------------------------------------------------------------------------
-- | Part 4: Alpha Conversion ----------------------------------------------
----------------------------------------------------------------------------
{-@ alpha :: ys:(S.Set Bndr) -> e:{Expr | isAbs e} -> {v:Expr | EqV v e} @-}
----------------------------------------------------------------------------
alpha ys (Abs x e) = Abs x' (subst (Var x') x e)
  where 
    xs             = free e
    x'             = freshS zs
    zs             = S.insert x (S.union ys xs)

alpha _  _         = liquidError "never"


----------------------------------------------------------------------------
-- | Part 3: Fresh Variables -----------------------------------------------
----------------------------------------------------------------------------
{-@ freshS :: xs:(S.Set Bndr) -> {v:Bndr | NotElem v xs} @-}
----------------------------------------------------------------------------
freshS xs = undefined


----------------------------------------------------------------------------
-- | Part 2: Free Variables ------------------------------------------------
----------------------------------------------------------------------------

----------------------------------------------------------------------------
{-@ free         :: e:Expr -> {v : S.Set Bndr | v = fv e} @-}
----------------------------------------------------------------------------
free (Var x)     = S.singleton x
free (App e e')  = S.union  (free e) (free e')
free (Abs x e)   = S.delete x (free e)


