
module Eval where 

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

data Expr = I     Int
          | B     Bool
          | Equal Expr Expr
          | Plus  Expr Expr
          deriving (Eq, Show)


{-@ check          :: e:ValidExpr  -> {v:Ty | (v = (eType e))} @-}
check (I _)        = TInt
check (B _)        = TBool
check (Plus e1 e2) = TInt
check (Equal _ _)  = TBool

{-@ Strict eval @-}

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

-- | The next two are silly, for scraping quals. Yuck. Should scrape from measure-DEFS etc.

{-@ toInt :: IntExpr -> Int @-}
toInt (I i) = i
toInt _     = liquidError "impossible"

{-@ toBool :: BoolExpr -> Bool @-}
toBool (B b) = b
toBool _     = liquidError "impossible"


{-@ predicate TInt X   = ((eType X) = TInt)  @-}
{-@ predicate TBool X  = ((eType X) = TBool) @-}


{-@ type ValidExpr     = {v: Expr | (isValid v)}                @-}
{-@ type IntExpr       = {v: Expr | ((isValue v) && (TInt  v))} @-}
{-@ type BoolExpr      = {v: Expr | ((isValue v) && (TBool v))} @-}


{-@ measure isValue       :: Expr -> Prop
    isValue (I i)         = true
    isValue (B b)         = true
    isValue (Equal e1 e2) = false 
    isValue (Plus e1 e2)  = false
  @-}  

{-@ measure eType       :: Expr -> Ty 
    eType (I i)         = TInt  
    eType (Plus  e1 e2) = TInt 
    eType (B b)         = TBool 
    eType (Equal e1 e2) = TBool 
  @-}

{-@ measure isValid       :: Expr -> Prop
    isValid (I i)         = true
    isValid (B b)         = true
    isValid (Equal e1 e2) = (((eType e1) = (eType e2)) && (isValid e1) && (isValid e2))
    isValid (Plus e1 e2)  = ((TInt e1) && (TInt e2) && (isValid e1) && (isValid e2))
  @-}

