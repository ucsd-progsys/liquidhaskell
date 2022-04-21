{-# LANGUAGE GADTs            #-}
{- LIQUID "--no-termination" @-}
{-@ LIQUID "--reflection"    @-}
{-@ LIQUID "--ple"            @-}


module IndLast where

-- | Lists ---------------------------------------------------------------------

data List a = Nil | Cons a (List a)

-- | List Membership -----------------------------------------------------------

data LastP a where
  Last :: a -> List a -> LastP a

data Last a where
  End :: a -> Last a 
  Mid :: a -> a -> List a -> Last a -> Last a 

{-@ data Last [pfSize] a where
        End :: x:a -> Prop (Last x (Cons x Nil))
        Mid :: x:a -> y:a -> ys:List a 
            -> Prop (Last x ys) 
            -> Prop (Last x (Cons y ys))
  @-}

{-@ reflect lastFun @-}
lastFun :: List a -> Maybe a 
lastFun Nil          = Nothing 
lastFun (Cons x Nil) = Just x 
lastFun (Cons _ t)   = lastFun t

{-@ last_fun_ok :: x:a -> l:List a -> Prop (Last x l) -> {lastFun l = Just x} @-}
last_fun_ok :: a -> List a -> Last a -> () 

last_fun_ok x _            (End _)                = () 
last_fun_ok x (Cons y Nil) (Mid _ _ ys last_x_ys) = last_fun_ok x ys last_x_ys
last_fun_ok x (Cons y ys)  (Mid _ _ _ last_x_ys)  = last_fun_ok x ys last_x_ys

{-@ measure prop :: a -> b           @-}
{-@ type Prop E = {v:_ | prop v = E} @-}

{-@ measure pfSize @-}
{-@ pfSize :: Last a -> Nat @-}
pfSize :: Last a -> Int
pfSize (End _)       = 0
pfSize (Mid _ _ _ t) = 1 + pfSize t
