
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ExtendedDefaultRules #-}

{-@ LIQUID "--higherorder"      @-}
{-@ LIQUID "--autoproofs"      @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
module Append where

import Axiomatize
import Equational

{-@ funEq :: m1:a  -> m2:{v:a | v == m1} -> {v: Proof | (\y:a -> m1) == (\x:a -> m2)} @-}
funEq :: a  -> a -> Proof 
funEq _ _ = Proof


{-@ funApp :: m1:a  -> m2:{v:a | v == m1} -> {v: Proof | (\y:a -> m1) (m1) == ((\x:a -> m2)) (m2) } @-}
funApp :: a  -> a -> Proof 
funApp _ _ = Proof

