module Foo () where
-- TODO: get this working with the ! annots.

import Language.Haskell.Liquid.Prelude
-- remove the ! and it is safe...
data MaybeS a = NothingS | JustS !a
-- (SAFE) data MaybeS a = NothingS | JustS a

{-@ measure isJustS :: forall a. MaybeS a -> Prop 
    isJustS (JustS x)  = true
    isJustS (NothingS) = false
  @-}

{-@ measure fromJustS :: forall a. MaybeS a -> a
    fromJustS (JustS x) = x 
  @-}

gloop = poop True

{-@ poop :: z:a -> {v: MaybeS a | fromJustS(v) = z} @-}
poop z = JustS z



























