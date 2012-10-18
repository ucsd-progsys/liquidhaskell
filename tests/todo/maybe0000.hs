module Foo where

data MaybeS a = NothingS | JustS a

-- crashes with : 
-- Fixpoint: Testing Solution 
-- z3Pred: error converting && [ (isJust(lq_anf__ddc) <=> false)
--                             ; (lq_anf__ddc = ds_dd9)
--                             ; (fromJustS([gloop#r9K]) = True#6u)
--                             ; (Bexp True#6u)
--                             ; (~ ((Bexp False#68)))]
--
-- Fatal error: exception Failure("Z3: type error")


myisJust :: Maybe a -> Bool
myisJust Nothing  = True
myisJust (Just x) = False

{-@ measure fromJustS :: MaybeS a -> a
    fromJustS (JustS x) = x 
  @-}

gloop :: MaybeS Bool
gloop = poop True

{- poop :: z:a -> {v: MaybeS a | fromJustS(v) = z} @-}
poop z = JustS z



























