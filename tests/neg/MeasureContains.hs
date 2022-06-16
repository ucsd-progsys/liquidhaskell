{-@ LIQUID "--expect-any-error" @-}
module MeasureContains where

import Language.Haskell.Liquid.Prelude

{-@ LIQUID "--no-termination" @-}

{-@ measure binderContainsV @-}
binderContainsV ::  Binder n -> Bool
binderContainsV B     = True
binderContainsV (M x) = containsV x

data Binder n = B | M (TT n)
data TT n     = V Int | Other | Bind (Binder n) (TT n)

{-@ measure containsV @-}
containsV :: TT n -> Bool
containsV (V i)         = True
containsV (Bind b body) = (binderContainsV b) || (containsV body)
containsV _             = False


prop1 = liquidAssert (containsV $ Other)
