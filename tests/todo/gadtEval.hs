-- | NAME resolution is all f-ed up. Why does Eval.TInt not get resolved? 
module Eval (
    Expr (..)
  , Ty (..)
  , eval
  , toInt
  , toBool
  ) where

import Language.Haskell.Liquid.Prelude (liquidError)

-- "Classic" GADT 
-- 
-- data Expr a where
--   I :: Int -> Expr Int
--   B :: Bool -> Expr Bool
--   Eq :: Expr a -> Expr a -> Expr Bool
--   Pl :: Expr Int -> Expr Int -> Expr Int
-- 
-- eval :: Expr a -> a
-- eval (I i)      = i
-- eval (B b)      = b
-- eval (Eq e1 e2) = (eval e1) == (eval e2)
-- eval (Pl e1 e2) = (eval e1) + (eval e2)

data Ty   = TInt 
          | TBool

-- foo True  = TInt
-- foo False = TBool

data Expr = I     Int
          | B     Bool
          | Equal Expr Expr
          | Plus  Expr Expr
          deriving (Eq, Show)

check (I _)       = TInt
check (B _)       = TBool
check (Plus _ _)  = TInt
check (Equal _ _) = TBool

{-@ eval           :: e:ValidExpr  -> {v:ValidExpr | ((isValue v) && (((eType e) = (eType v))))} @-}
eval e@(I _)       = e
eval e@(B _)       = e
eval (Plus e1 e2)  = (eval e1) `plus` (eval e2)
eval (Equal e1 e2) = (eval e1) `equal` (eval e2)

plus (I i) (I j)   = I (i + j)
plus _       _     = liquidError "don't worry, its impossible" 

equal (I i) (I j)  = B (i == j)
equal (B x) (B y)  = B (x == y)
equal _       _    = liquidError "don't worry, its impossible" 

-- | The next two are silly, for scraping quals. Yuck. 
-- Should scrape from DEFS etc.

{-@ toInt :: IntExpr -> Int @-}
toInt (I i) = i
toInt _     = liquidError "impossible"

{-@ toBool :: BoolExpr -> Bool @-}
toBool (B b) = b
toBool _     = liquidError "impossible"


{- predicate TInt X   = ((eType X) = 0) @-}
{- predicate TBool X  = ((eType X) = 1) @-}


{-@ type ValidExpr     = {v: Expr | (isValid v)                             } @-}
{-@ type IntExpr       = {v: Expr | ((isValue v) && ((eType v) = Eval.TInt))} @-}
{-@ type BoolExpr      = {v: Expr | ((isValue v) && ((eType v) = Eval.TBool))} @-}

{-@ measure isValue       :: Expr -> Prop
    isValue (I i)         = true
    isValue (B b)         = true
    isValue (Equal e1 e2) = false 
    isValue (Plus e1 e2)  = false
  @-}  

{-@ measure eType       :: Expr -> Ty 
    eType (I i)         = Eval.TInt  
    eType (Plus  e1 e2) = Eval.TInt 
    eType (B b)         = Eval.TBool 
    eType (Equal e1 e2) = Eval.TBool 
  @-}

{-@ measure isValid       :: Expr -> Prop
    isValid (I i)         = true
    isValid (B b)         = true
    isValid (Equal e1 e2) = (((eType e1) = (eType e2)) && (isValid e1) && (isValid e2))
    isValid (Plus e1 e2)  = (((eType e1) = Eval.TInt) && ((eType e2) = Eval.TInt) && (isValid e1) && (isValid e2))
  @-}



