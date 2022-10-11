{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE GADTs           #-}
{-# LANGUAGE KindSignatures  #-}

{-@ LIQUID "--reflection"  @-} 
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--fast"        @-}

module T1660 where

import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (id, fmap)

{-@ measure eqT :: a -> a -> Bool @-}
{-@ type EqRT a E1 E2 = {v:EqT a | eqT E1 E2} @-}

data EqT  :: * -> *  where 
   EqSMT  :: Eq a => a -> a -> () -> EqT a 
   EqFun  :: (a -> b) -> (a -> b) -> (a -> EqT b) -> EqT (a -> b)

{-@ data EqT  :: * -> *  where 
       EqSMT  :: Eq a => x:a -> y:a -> {v:() | x == y} -> EqRT a {x} {y}
       EqFun  :: ff:(a -> b) -> gg:(a -> b) -> (x:a -> {v:EqT b | eqT (ff x) (gg x)}) -> EqRT (a -> b) {ff} {gg}
@-}   


type Reader a b = a -> b



functorLaw_identity :: Eq a => EqT (Reader r a -> Reader r a)
{-@ functorLaw_identity :: Eq a -> EqRT (Reader r a -> Reader r a) (fmap id) id @-}
functorLaw_identity =
  EqFun (fmap id) id
  (\r -> EqFun (fmap id r) (id r)
    (\a -> EqSMT (fmap id r a) (id r a? lemmaId r a) ()))

{-@ reflect id @-}
id :: a -> a 
id x = x

{-@ reflect fmap @-}
fmap :: (a -> b) -> Reader r a -> Reader r b
fmap fab fra = \r -> fab (fra r)

lemmaId :: Eq b => (a -> b) -> a -> ()
{-@ lemmaId :: f:(a -> b) -> x:a -> {id f x = id (f x) } @-}
lemmaId _ _ = ()
