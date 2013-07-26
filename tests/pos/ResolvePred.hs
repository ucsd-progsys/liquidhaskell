module ResolvePred where

data L = C Int L | N

{-@ myFold :: forall <q :: L -> b -> Prop>.
              (as:L -> a:Int -> b<q as> -> b<q (C a as)>)
           -> b<q N>
           -> l:L
           -> b<q l>
  @-}
myFold f z = go
  where
    go N       = z
    go (C a as) = f as a (go as)
