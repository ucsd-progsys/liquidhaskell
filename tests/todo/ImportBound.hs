module ImportBound where

data Proof

{-@ bound chain @-}
chain :: (Proof -> Bool) -> (Proof -> Bool) -> (Proof -> Bool)
      -> Proof -> Bool
chain p q r = \v -> p v

{-@  by :: forall <p :: Proof -> Prop, q :: Proof -> Prop, r :: Proof -> Prop>.
                 (Chain p q r) => Proof<p> -> Proof<q> -> Proof<r>
@-}
by :: Proof -> Proof -> Proof
by _ r = r
