{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--no-termination" @-}


import Language.Haskell.Liquid.NewProofCombinators 
import Prelude hiding ((++))

data List a = Emp 

{-@ infixr ++ @-}

{-@ reflect ++ @-}
Emp ++ ys = ys

{-@ assocPf :: xs:_ -> ys:_  -> { (xs ++ ys) == ys  } @-}
assocPf :: List a -> List a  -> Proof 

assocPf Emp ys
  =   (Emp ++ ys) 
  === ys 
  *** QED