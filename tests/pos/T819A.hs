import Language.Haskell.Liquid.ProofCombinators 

import Prelude hiding ((++))

{-@ LIQUID "--exactdc"        @-}
{-@ LIQUID "--no-termination" @-}

{-@ data List  a = Emp  @-}
data List a = Emp 


{-@ infixr ++ @-}

{-@ reflect ++ @-}
Emp ++ ys = ys


{-@ assocPf :: xs:_ -> ys:_  -> { (xs ++ ys) == ys  } @-}
assocPf :: List a -> List a  -> Proof 

assocPf Emp ys
  =   (Emp ++ ys) 
  ==. ys 
  *** QED