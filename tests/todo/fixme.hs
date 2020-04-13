{-@ LIQUID "--reflection" @-} 

{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE GADTs           #-}
{-# LANGUAGE KindSignatures  #-}

module RefinedEquality
  ( EqT()
  , eqRTCtx
  , eqFun
  , eqSMT
  ) where 

import Language.Haskell.Liquid.ProofCombinators

{-@ measure eqT :: a -> a -> Bool @-}
{-@ type EqRT a E1 E2 = {v:EqT a | eqT E1 E2} @-}


{-@ eqRTCtx :: x:a -> y:a -> EqRT a {x} {y} -> ctx:(a -> b) -> EqRT b {ctx x} {ctx y}  @-}
eqRTCtx ::  a -> a -> EqT a -> (a -> b) -> EqT b
eqRTCtx = undefined   

{-@ eqFun :: f:(a -> b) -> g:(a -> b) 
          -> (x:a -> {v:EqT b | eqT (f x) (g x)}) -> EqRT (a -> b) {f} {g}  @-}
eqFun :: (a -> b) -> (a -> b) -> (a -> EqT b) -> EqT (a -> b)
eqFun = EqFun

{-@ eqSMT :: Eq a => x:a -> y:a -> {v:() | x == y} -> EqRT a {x} {y} @-}
eqSMT :: Eq a => a -> a -> () -> EqT a
eqSMT = EqSMT 

data EqT  :: * -> *  where 
   EqSMT  :: Eq a => a -> a -> () -> EqT a 
   EqFun  :: (a -> b) -> (a -> b) -> (a -> EqT b) -> EqT (a -> b)
   EqCtx  :: a -> a -> EqT a -> (a -> b) -> EqT b 

{-@ data EqT  :: * -> *  where 
     EqSMT  :: Eq a => x:a -> y:a -> {v:() | x == y} -> EqRT a {x} {y}
   | EqFun  :: ff:(a -> b) -> gg:(a -> b) -> (x:a -> {v:EqT b | eqT (ff x) (gg x)}) -> EqRT (a -> b) {ff} {gg}
   | EqCtx  :: x:a -> y:a -> EqRT a {x} {y} -> ctx:(a -> b) -> EqRT b {ctx x} {ctx y} 
@-}   
