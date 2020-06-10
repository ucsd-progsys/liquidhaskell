import Language.Haskell.Liquid.ProofCombinators

import Prelude hiding (sum, range)

{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--exactdc" @-}

{-@ natinduction :: p:(Nat-> Bool) -> PAnd {v:Proof | p 0} (n:Nat -> {v:Proof | p (n-1)} -> {v:Proof | p n})
                 -> n:Nat -> {v:Proof | p n}  @-}
natinduction :: (Int-> Bool) -> PAnd Proof (Int -> Proof -> Proof)-> Int -> Proof 
natinduction p (PAnd p0 pi) n  
  | n == 0    = p0 
  | otherwise = pi n (natinduction p (PAnd p0 pi) (n-1))


-- Example of proving with natinduction 

{-@ prop :: n:Nat -> {godelProp n} @-} 
prop :: Int -> Proof 
prop n = natinduction godelProp (PAnd baseCase indCase) n


{-@ assume indCase :: n:Nat -> {v:Proof | godelProp (n-1)} -> {v:Proof | godelProp n} @-} 
indCase :: Int -> Proof -> Proof 
indCase _ _ = ()
    
{-@ assume baseCase :: {godelProp 0} @-} 
baseCase :: Proof 
baseCase = ()

{-@ reflect godelProp@-}
godelProp :: Int -> Bool 
godelProp n = n == n

data POr  a b = POrLeft a | POrRight b 
data PAnd a b = PAnd a b 

main :: IO ()
main = pure ()
