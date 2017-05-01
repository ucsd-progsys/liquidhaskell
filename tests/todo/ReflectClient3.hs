
{-@ LIQUID "--totality"                            @-}
{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module ReflectClient3 where

import Language.Haskell.Liquid.ProofCombinators
import ReflectLib3

stupidity = [ undefined llen ]

{-@ test3 :: { llen Nil == 0 } @-}
test3 = ()

-- THIS FAILS
{-@ zoo :: List a -> {v:Int | v == 0} @-}
zoo :: List a -> Int
zoo Nil         = llen Nil
zoo (Cons x xs) = 0

-- BUT ADDING THIS MAKES EVERYTHING WORK
{-@ moo :: List a -> {v:Int | v == 0} @-}
moo :: List a -> Int
moo Nil         = ben Nil
moo (Cons x xs) = moo xs
