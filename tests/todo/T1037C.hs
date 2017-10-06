{-# LANGUAGE TypeFamilies #-}
module T1037C where

import Language.Haskell.Liquid.ProofCombinators

class Generic a where
  type Rep a :: * -> *
  from :: a -> Rep a x
  to   :: Rep a x -> a
