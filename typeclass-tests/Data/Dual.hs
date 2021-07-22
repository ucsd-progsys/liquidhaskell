{-# LANGUAGE RankNTypes #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}


module Data.Dual where

{-@ data Dual a = Dual {getDual :: a} @-}
data Dual a = Dual {getDual :: a}
