{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module DependeTypes where

import GHC.TypeLits


-- THIS SHOULD BE SAFE 
misafe   :: MI "blaa" 
misafe   = Small "blaa"


data MI (s :: Symbol)
  = Small { mi_input :: String  }


{-@ Small :: forall (s :: Symbol). {v:String | s ~~ v } -> MI s @-}

-- OR 

{- data MI (s :: Symbol)
    = Small { mi_input :: {v:String | v == s } } @-}
