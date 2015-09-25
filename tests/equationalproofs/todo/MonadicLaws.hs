module Monadic where

import Language.Haskell.Liquid.Prelude ((==>))




class MyMonad m where
  unit :: a -> m a
  bind :: m a -> (a -> m b) -> m b


data Arrow a b = A {runFun ::  a -> b}


-- | Express Left Identity

{-@ measure runFun :: (Arrow a b) -> a -> b @-}

{-@ prop_left_identity :: unit:(Arrow a (m a)) -> bind:(Arrow (m a) (Arrow (Arrow a (m b)) (m b)) )
                      -> x:a -> f:(Arrow a (m b))
                      -> {v:Proof | runFun (runFun bind (runFun unit x)) f  == runFun f x }
  @-}

prop_left_identity :: (Arrow a (m a)) -> (Arrow (m a) (Arrow (Arrow a (m b)) (m b)))
                    -> a -> (Arrow a (m b))
                    -> Proof
prop_left_identity iunit ibind x f = Proof

-- | Express Left Identity in Haskell

prop_left_identity_HS :: (Eq (m a), Eq (m b)) => (Arrow a (m a)) -> (Arrow (m a) (Arrow (Arrow a (m b)) (m b)))
                      -> a -> (Arrow a (m b))
                      -> Bool
prop_left_identity_HS unit bind x f
  = runFun (runFun bind (runFun unit x)) f == runFun f x



-- | Proof library:

data Proof = Proof


{-@ toProof :: l:a -> r:{a|l = r} -> {v:Proof | l = r } @-}
toProof :: a -> a -> Proof
toProof x y = Proof


{-@ (===) :: l:a -> r:a -> {v:Proof | l = r} -> {v:a | v = l } @-}
(===) :: a -> a -> Proof -> a
(===) x y _ = y

-- | Proof: map
{-@ type Equal X Y = {v:Proof | X == Y} @-}

{- invariant {v:Proof | v == Proof } @-}

{-@ bound chain @-}
chain :: (Proof -> Bool) -> (Proof -> Bool) -> (Proof -> Bool) -> Proof -> Bool
chain p q r v = p v ==> q v ==> r v

{-@  assume by :: forall <p :: Proof -> Prop, q :: Proof -> Prop, r :: Proof -> Prop>.
                 (Chain p q r) => Proof<p> -> Proof<q> -> Proof<r>
@-}
by :: Proof -> Proof -> Proof
by p r = r

{-@ refl :: x:a -> Equal x x @-}
refl :: a -> Proof
refl x = Proof

-- | End library
