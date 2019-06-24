{-@ LIQUID "--reflection" @-}
module Logic where 

{- 
    ϕ ≡ (∃x.∀y.(p x y)) ⇒ (∀y.∃x.(p x y))
 -}

φ :: (a -> a -> Bool) 
  -> (a, a -> Bool)
  -> a -> (a, Bool)
 
{-@
φ :: p:(a -> a -> Bool) 
  -> (x::a, y:a -> {p x y})
  -> z:a -> (w::a, {p w z})
@-}
φ p (x, pxy) = \y -> (x, pxy y) 