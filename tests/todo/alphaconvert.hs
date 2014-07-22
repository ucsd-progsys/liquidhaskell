{-@ LIQUID "--no-termination" @-}

module AlphaConvert () where

import Data.List        (lookup)
import Prelude hiding ((++))
import Language.Haskell.Liquid.Prelude   

---------------------------------------------------------------------
-- | Datatype Definition --------------------------------------------
---------------------------------------------------------------------

type Bndr 
  = Int

data Expr 
  = Var Bndr  
  | Abs Bndr Expr
  | App Expr Expr

---------------------------------------------------------------------
-- | Alpha Conversion -----------------------------------------------
---------------------------------------------------------------------

alpha              :: [Bndr] -> Expr -> Expr
alpha ys (Abs x e) = Abs x' ((x, Var x') `subst` e)
  where 
    xs             = free e
    x'             = fresh (x : ys ++ xs)

alpha _            = error "liquidError: never"


subst            :: (Bndr, Expr) -> Expr -> Expr

subst (x, e') e@(Var y)
  | x == y                = e' 
  | otherwise             = e

subst (x, e') (App ea eb) = App ea' eb'
  where
    ea'                   = (x, e') `subst` ea
    eb'                   = (x, e') `subst` eb

subst (x, e') e@(Abs y e'')   
  | x == y                = e
  | y `elem` xs           = (x, e') `subst` (alpha xs e) 
  | otherwise             = Abs y ((x, e') `subst` e'') 
  where
    xs                    = free e'  

fresh     :: [Bndr] -> [Bndr]
fresh xs  = error "TODO"

---------------------------------------------------------------------
-- | Free Variables -------------------------------------------------
---------------------------------------------------------------------

free             :: Expr -> [Bndr]
free (Var x)     = [x]
free (App e e')  = free e ++ free e'
free (Abs x e)   = free e \\ x


---------------------------------------------------------------------
-- | Sets with Lists ------------------------------------------------
---------------------------------------------------------------------

(++)                 :: [a] -> [a] -> [a]
[]     ++ ys         = ys
(x:xs) ++ ys         = x : (xs ++ ys)

(\\)                 :: (Eq a) => [a] -> a -> [a]
xs \\ y              = [x | x <- xs, x /= y]

elem                 :: (Eq a) => a -> [a] -> Bool
elem x []            = False
elem x (y:ys)        = x == y || elem x ys

