module Interpreter where 

{- The following code crashes fixpoint see issue 
https://github.com/ucsd-progsys/liquid-fixpoint/issues/77
-}

data List a = Nil 

{-@ measure progDenote :: List Int -> Maybe (List Int) @-}
{-@ compile :: {v:Bool | (progDenote Nil) == Nothing } @-}
compile :: Bool
compile = undefined 
