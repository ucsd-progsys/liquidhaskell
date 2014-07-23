{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--fullcheck"      @-}

module AlphaConvert () where

import Prelude hiding ((++), elem)
import Data.Set (Set (..))
-- import Language.Haskell.Liquid.Prelude   

maxs    :: [Int] -> Int 
lemma1  :: Int -> [Int] -> Bool
fresh   :: [Bndr] -> Bndr
free    :: Expr -> [Bndr]

liquidError  = undefined
liquidAssert = undefined
liquidAssume = undefined

---------------------------------------------------------------------
-- | Datatype Definition --------------------------------------------
---------------------------------------------------------------------

type Bndr 
  = Int

data Expr 
  = Var Bndr  
  | Abs Bndr Expr
  | App Expr Expr

{-@ measure fv       :: Expr -> (Set Bndr)
    fv (Var x)       = (Set_sng x)
    fv (Abs x e)     = (Set_dif (fv e) (Set_sng x))
    fv (App e a)     = (Set_cup (fv e) (fv a)) 
  @-}

{-@ measure isAbs    :: Expr -> Prop
    isAbs (Var v)    = false
    isAbs (Abs v e)  = true
    isAbs (App e a)  = false             
  @-}

{-@ predicate AddV E E2 X E1  = fv E = Set_cup (Set_dif (fv E2) (Set_sng X)) (fv E1) @-}
{-@ predicate EqV E1 E2       = fv E1 = fv E2                                        @-}
{-@ predicate Occ X E         = Set_mem X (fv E)                                     @-}
{-@ predicate Subst V E1 X E2 = if (Occ X E2) then (AddV V E2 X E1) else (EqV V E2)  @-}

----------------------------------------------------------------------------
-- | Part 5: Capture Avoiding Substitution ---------------------------------
----------------------------------------------------------------------------
{-@ subst :: e1:Expr -> x:Bndr -> e2:Expr -> {v:Expr | Subst v e1 x e2} @-} 
----------------------------------------------------------------------------
subst e' x e@(Var y)
  | x == y                = e' 
  | otherwise             = e

subst e' x (App ea eb)    = App ea' eb'
  where
    ea'                   = subst e' x ea
    eb'                   = subst e' x eb

subst e' x e@(Abs y e'')   
  | x == y                = e
  | y `elem` xs           = subst e' x (alpha xs e) 
  | otherwise             = Abs y (subst e' x e'') 
  where
    xs                    = free e'  

----------------------------------------------------------------------------
-- | Part 4: Alpha Conversion ----------------------------------------------
----------------------------------------------------------------------------
{-@ alpha :: ys:[Bndr] -> e:{Expr | isAbs e} -> {v:Expr | EqV v e} @-}
----------------------------------------------------------------------------
alpha ys (Abs x e) = Abs x' (subst (Var x') x e)
  where 
    xs             = free e
    x'             = fresh (x : ys ++ xs)

alpha _  _         = liquidError "never"


----------------------------------------------------------------------------
-- | Part 3: Fresh Variables -----------------------------------------------
----------------------------------------------------------------------------
{-@ fresh :: xs:[Bndr] -> {v:Bndr | NotElem v xs} @-}
----------------------------------------------------------------------------
fresh bs = liquidAssert (lemma1 n bs) n
  where 
    n    = 1 + maxs bs

{-@ maxs :: xs:_ -> {v:_ | v = maxs xs} @-}
maxs ([])   = 0
maxs (x:xs) = if x > maxs xs then x else (maxs xs) 
 
 
{-@ measure maxs :: [Int] -> Int 
    maxs ([])   = 0
    maxs (x:xs) = if (x > maxs xs) then x else (maxs xs) 
  @-}

{-@ lemma1 :: x:Int -> xs:{[Int] | x > maxs xs} -> {v:Bool | Prop v && NotElem x xs} @-}
lemma1 x []     = True 
lemma1 x (y:ys) = lemma1 x ys 


----------------------------------------------------------------------------
-- | Part 2: Free Variables ------------------------------------------------
----------------------------------------------------------------------------

----------------------------------------------------------------------------
{-@ free         :: e:Expr -> {v:[Bndr] | elts v = fv e} @-}
----------------------------------------------------------------------------
free (Var x)     = [x]
free (App e e')  = free e ++ free e'
free (Abs x e)   = free e \\ x


----------------------------------------------------------------------------
-- | Part I: Sets with Lists -----------------------------------------------
----------------------------------------------------------------------------

{-@ predicate IsCup X Y Z  = elts X = Set_cup (elts Y) (elts Z)    @-}
{-@ predicate IsEq X Y     = elts X = elts Y                       @-}
{-@ predicate IsDel X Y Z  = elts X = Set_dif (elts Y) (Set_sng Z) @-}
{-@ predicate Elem  X Ys   = Set_mem X (elts Ys)                   @-}
{-@ predicate NotElem X Ys = not (Elem X Ys)                       @-}

{-@ (++)      :: xs:[a] -> ys:[a] -> {v:[a] | IsCup v xs ys}  @-}
[]     ++ ys  = ys
(x:xs) ++ ys  = x : (xs ++ ys)

{-@ (\\)      :: (Eq a) => xs:[a] -> y:a -> {v:[a] | IsDel v xs y} @-}
xs   \\ y     = [x | x <- xs, x /= y]

{-@ elem      :: (Eq a) => x:a -> ys:[a] -> {v:Bool | Prop v <=> Elem x ys} @-}
elem x []     = False
elem x (y:ys) = x == y || elem x ys
 
{-@ measure elts :: [a] -> (Set a) 
    elts ([])    = {v | Set_emp v}
    elts (x:xs)  = {v | v = Set_cup (Set_sng x) (elts xs) }
  @-}
