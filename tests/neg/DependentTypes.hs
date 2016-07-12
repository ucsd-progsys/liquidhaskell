{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module DependeTypes where

import GHC.TypeLits



-- THIS SHOULD BE UNSAFE
miunsafe1 :: forall s. MI s 
miunsafe1 = Small "blaa"

-- THIS SHOULD BE UNSAFE 
miunsafe2 :: MI "bla0" 
miunsafe2 = Small "blaa"


data MI (s :: Symbol)
  = Small { mi_input :: String  }


{-@ Small :: forall (s :: Symbol). {v:String | s ~~ v } -> MI s @-}

-- OR 

{- data MI (s :: Symbol)
    = Small { mi_input :: {v:String | v == s } } @-}
