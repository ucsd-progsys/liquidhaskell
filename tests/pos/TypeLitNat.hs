{-# LANGUAGE GADTs #-}

{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

module TypeLitNat where

import GHC.TypeLits

-- THIS SHOULD BE UNSAFE
miunsafe2 :: MI 0
miunsafe2 = Small 0

data MI (s :: Nat) = Small { mi_input :: Int  }

{-@ Small :: forall (s :: Nat). {v:Int | s ~~ v } -> MI s @-}
