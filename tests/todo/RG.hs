{- this is a test for the "bug" introduced in liquid-fixpoint by 
   commit: 9608cb6e4dd33bf142b50db4630c629defceb91e             -}

module RG where

data RGRef a

{-@ measure tv :: RGRef a -> a @-}

{-@ qualif TERMINALVALUE(r:RGRef a): (tv r) @-}


