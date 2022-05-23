{-# LANGUAGE BangPatterns #-}
module BangPatterns where

import Data.IORef

import Language.Haskell.Liquid.Prelude

foo :: IORef a -> IORef a
{-@ foo :: x:IORef a -> {v:IORef a |  v = x} @-}
foo !x = x
