module ListSort where


data P a = P a Int

{-@ data P a <p :: a -> Int -> Prop>
     = P (i :: a) (v :: Int<p i>)
  @-}
{-@ type OP  = P <{\p v ->  p > v}> Int @-}

foo :: P Int
{-@ foo :: OP @-}
foo = P 3 2
