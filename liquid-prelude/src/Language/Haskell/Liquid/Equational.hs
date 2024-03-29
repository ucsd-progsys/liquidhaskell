{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
module Language.Haskell.Liquid.Equational where 

-------------------------------------------------------------------------------
-- | Proof is just unit
-------------------------------------------------------------------------------

type Proof = ()

-------------------------------------------------------------------------------
-- | Casting expressions to Proof using the "postfix" `*** QED` 
-------------------------------------------------------------------------------

data QED = QED 

infixl 2 ***
(***) :: a -> QED -> Proof
_ *** QED = () 

-------------------------------------------------------------------------------
-- | Equational Reasoning operators 
-- | The `eq` operator is inlined in the logic, so can be used in reflected 
-- | functions while ignoring the equality steps. 
-------------------------------------------------------------------------------

infixl 3 ==., `eq` 


{-@ (==.) :: x:a -> y:{a | x == y} -> {v:a | v == y && v == x} @-}
(==.) :: a -> a -> a 
_ ==. x = x 
{-# INLINE (==.) #-} 


{-@ eq :: x:a -> y:{a | x == y} -> {v:a | v == y && v == x} @-}
eq :: a -> a -> a 
_ `eq` x = x 
{-# INLINE eq #-} 

-------------------------------------------------------------------------------
-- | Explanations
-------------------------------------------------------------------------------

infixl 3 ?

{-@ (?) :: forall a b <pa :: a -> Bool>. a<pa> -> b -> a<pa> @-}
(?) :: a -> b -> a 
x ? _ = x 
{-# INLINE (?)   #-} 

-------------------------------------------------------------------------------
-- | Using proofs as theorems 
-------------------------------------------------------------------------------

withTheorem :: a -> Proof -> a 
withTheorem z _ = z 
