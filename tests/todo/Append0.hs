module Reverse where

{-@ LIQUID "--no-termination" @-}

import Prelude hiding (reverse)

data List a = N | C a (List a)

{-@ measure reverse @-}

reverse :: List a -> List a -> List a
reverse zs N        = zs 
reverse zs (C y ys) = C y (reverse zs ys)