{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-} 

module ReflectLib3 where

import Language.Haskell.Liquid.ProofCombinators

-- | Days ---------------------------------------------------------------------

{-@ data Day = Mon | Tue @-}
data Day = Mon | Tue

{-@ reflect next @-}
next :: Day -> Day
next Mon = Tue
next Tue = Mon

-- | Lists ---------------------------------------------------------------------

{-@ data List  a = Nil | Cons {lHd :: a} @-}
data List a = Nil | Cons a

{-@ reflect lDay @-}
lDay :: List a -> Day
lDay Nil      = Mon
lDay (Cons x) = Tue
