{-@ LIQUID "--pruneunsorted" @-}

module ResolvePred (myFold, llen) where

{-@ data L [llen] = C (h :: Int) (t :: L) | N @-}

data L = C Int L | N

{-@ myFold :: forall <q :: L -> b -> Bool>.
              (as:L -> a:Int -> b<q as> -> b<q (C a as)>)
           -> b<q N>
           -> l:L
           -> b<q l>
  @-}
myFold f z = go
  where
    go N       = z
    go (C a as) = f as a (go as)

{-@ measure llen @-}
llen :: L -> Int
{-@ llen :: L -> Nat @-}
llen N      = 0
llen (C _ xs) = 1 + (llen xs)

{-@ qualif PappL(v:a, p:Pred a L , a:int, as:L ):
        papp2(p, v, C(a, as))
  @-}
