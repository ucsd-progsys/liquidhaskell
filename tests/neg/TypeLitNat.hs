{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module DependeTypes where

import GHC.TypeLits



-- THIS SHOULD BE UNSAFE
miunsafe1 :: forall s. MI s 
miunsafe1 = Small 0

-- THIS SHOULD BE UNSAFE 
miunsafe2 :: MI 0 
miunsafe2 = Small 10


data MI (s :: Nat)
  = Small { mi_input :: Int  }


{-@ Small :: forall (s :: Nat). {v:Int | s ~~ v } -> MI s @-}

-- OR 

{- data MI (s :: Symbol)
    = Small { mi_input :: {v:String | v == s } } @-}
