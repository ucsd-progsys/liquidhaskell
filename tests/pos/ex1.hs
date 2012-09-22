module Ex where

-- | Testing "existential-types"

{-@ efoldr :: forall a <p :: x0:L a -> x1:b -> Bool>. 
                (xs:L a -> x:a -> b <p xs> -> exists [xxs : {v: L a | v = Cons x xs)}]. b<p xxs>) 
              -> (exists [x0: {v: L a | v = Nil}]. b <p x0>) 
              -> ys: L a
              -> b <p ys>
  @-}

efoldr :: (L a -> a -> b -> b) -> b -> L a -> b
efoldr op b Nil         = b
efoldr op b (Cons x xs) = op xs x (efoldr f b xs) 


{-@ size :: xs:L a -> {v: Int | v = llen(xs)} @-}
size :: L a -> Int
size = efoldr (\_ _ n -> n + 1) 0


app xs ys = efoldr (\_ -> Cons) ys xs 
