
{-@ LIQUID "--reflection" @-} 
{-@ LIQUID "--ple"        @-} 

module ReflectClient4 where

import Language.Haskell.Liquid.ProofCombinators

import ReflectLib4

-- THIS IS NEEDED TO BRING THE NAMES INTO SCOPE FOR GHC ...
forceImports = [ ]

{-@ test1 :: {v:List a | v = Nil} @-}
test1 :: List a
test1 = Nil


{-@ test2 :: {v:Proof | llen (Cons 1 Nil) = 1} @-}
test2 :: Proof
test2 =  llen (Cons 1 Nil)
      === 1 + llen Nil
      === 1
      *** QED

{-@ test3 :: {v:Proof | llen (Cons 1 (Cons 2 Nil)) = 2} @-}
test3 :: Proof
test3 =  llen (Cons 1 (Cons 2 Nil))
      === 1 + llen (Cons 2 Nil)
      === 1 + 1 + llen Nil
      *** QED

{-@ zen :: xs:List a -> {v:Nat | v = llen xs} @-}
zen :: List a -> Int
zen Nil        = 0
zen (Cons h t) = 1 + zen t

{-@ test5 :: { app (Cons 1 Nil) (Cons 2 (Cons 3 Nil)) = Cons 1 (Cons 2 (Cons 3 Nil)) } @-}
test5 =   app (Cons 1 Nil) (Cons 2 (Cons 3 Nil))
      === Cons 1 (app Nil (Cons 2 (Cons 3 Nil)))
      === Cons 1 (Cons 2 (Cons 3 Nil))
      *** QED

{-@ thmAppLen :: xs:List a -> ys:List a -> { llen (app xs ys) == llen xs + llen ys} @-}
thmAppLen :: List a -> List a -> Proof
thmAppLen Nil ys
  =  ()

thmAppLen (Cons x xs) ys
  = thmAppLen xs ys
