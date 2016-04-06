
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ExtendedDefaultRules #-}

{-@ LIQUID "--higherorder"      @-}
{-@ LIQUID "--autoproofs"      @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
module Append where

import Axiomatize
import Equational

{-@ helper :: m1:a  -> m2:{v:a | v == m1} -> {v: Proof | (\y:a -> m1) == (\x:a -> m2)} @-}
helper :: a  -> a -> Proof 
helper _ _ = Proof
