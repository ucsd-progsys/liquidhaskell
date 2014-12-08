module Fixme where

{-@ measure containsV @-}
{-@ measure binderContainsV @-}


binderContainsV ::  Binder n -> Bool
binderContainsV B = True

data Binder n = B
data TT n = P Int Int (TT n) | V Int | Other | Bind Int (Binder n) (TT n)

containsV :: TT n -> Bool
containsV (P nt n ty)     = containsV ty
containsV (V i)           = True
containsV (Bind n b body) = (binderContainsV b) || (containsV body)
-- containsV (App f arg)     = (containsV f) || (containsV arg)
-- containsV (Proj tm i)     = containsV tm
containsV _               = False