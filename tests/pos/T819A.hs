import Language.Haskell.Liquid.ProofCombinators 

import Prelude hiding ((++))

{-@ LIQUID "--exactdc" @-}
{-@ data List [llen] a = Emp | C {hd :: a, tl :: (List a)} @-}
data List a = Emp | C a  (List a)  deriving (Eq)

llen :: List a -> Int 
{-@ llen :: List a -> Nat @-}
{-@ measure llen @-}
llen Emp = 0 
llen (C _ xs) = 1 + llen xs


{-@ infixr ++ @-}

{-@ reflect ++ @-}
Emp ++        ys = ys
(x `C` xs) ++ ys = x `C` (xs ++ ys)

{-@ inline assocThm @-}
assocThm xs ys zs
  = (xs ++ ys) ++ zs == xs ++ (ys ++ zs)

{-@ assocPf :: xs:_ -> ys:_ -> zs:_ -> { assocThm xs ys zs } @-}
assocPf :: Eq a => List a -> List a -> List a -> Proof 

assocPf Emp ys zs
  =   (Emp ++ ys) ++ zs
  ==. ys ++ zs
  ==. Emp ++ (ys ++ zs)
  *** QED
assocPf (x `C` xs) ys zs
  =   ((x `C` xs) ++ ys) ++ zs
  ==. (x `C` (xs ++ ys)) ++ zs
  ==. x `C` ( (xs ++ ys) ++ zs)
  ==. x `C` (xs ++ (ys ++ zs)) ? assocPf xs ys zs
  ==. (x `C` xs) ++ (ys ++ zs)
  *** QED

  
