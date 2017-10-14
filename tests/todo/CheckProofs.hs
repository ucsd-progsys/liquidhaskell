import Language.Haskell.Liquid.ProofCombinators 


{-@ foo :: () -> Proof @-}
foo :: () -> Proof 
foo _ 
  =   1 
  ==. 2
  ==. 3 
  *** QED 