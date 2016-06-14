{-@ LIQUID "--pruneunsorted" @-}

module ResolvePred (myFold) where

{-@ data L [llen] = C (h :: Int) (t :: L) | N @-}
{-@ invariant {v:L | (llen v) >= 0} @-}

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

{-@ measure llen :: L -> Int
    llen (N)      = 0
    llen (C x xs) = 1 + (llen xs)
  @-}

{-@ qualif PappL(v:a, p:Pred a L , a:int, as:L ):
        papp2(p, v, C(a, as))
  @-}
