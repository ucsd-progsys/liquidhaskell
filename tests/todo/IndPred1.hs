{-@ LIQUID "--exact-data-con"                      @-}
{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--totality"                            @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module IndPred where

import Prelude hiding (sum)

--------------------------------------------------------------------------------

{-@ measure llen @-}
{-@ llen :: List a -> Nat @-}
llen :: List a -> Int
llen Nil        = 0
llen (Cons h t) = 1 + llen t

{-@ data List [llen] a = Nil | Cons {lHd :: a , lTl :: (List a) } @-}
data List a = Nil | Cons a (List a)

--------------------------------------------------------------------------------

data IsIns a
  = Here  { m :: a, ms :: List a }
  | There { m :: a, n :: a, ns :: List a, mns :: List a }

{-@ measure isIns :: a -> List a -> List a -> Bool @-}

-- v = Here m ms = isIns m ms (Cons m ms)



{-@ assume Here :: m:a
                -> ms:List a
                -> { v : IsIns a | isIns m ms (Cons m ms) }
  @-}

{-@ assume There :: m:a -> n:a -> ns:List a
                 -> mns:{List a | isIns m ns mns }
                 -> { v : IsIns a | isIns m (Cons n ns) (Cons n mns)}
  @-}

--------------------------------------------------------------------------------

data IsPerm a
  = NilPerm
  | ConsPerm { cm :: a, cms :: List a, cns :: List a, cmns :: List a }

{-@ measure isPerm  :: List a -> List a -> Bool @-}

{-@ assume NilPerm  :: {v:IsPerm a | isPerm Nil Nil} @-}

{-@ assume ConsPerm :: cm:a -> cms:List a
                    -> cns: {List a | isPerm cms cns   }
                    -> cmns:{List a | isIns cm cns cmns }
                    -> {v:IsPerm a | isPerm (Cons cm cms) cmns }
  @-}

--------------------------------------------------------------------------------

{-@ reflect sum @-}
sum :: List Int -> Int
sum Nil         = 0
sum (Cons x xs) = x + sum xs


{-@ lemma :: x:a -> ys:List a -> xys:List a
          -> {v:IsIns a | isIns x ys xys}
          -> { x + sum ys == sum xys}
  @-}
lemma :: a -> List a -> List a -> IsIns a -> ()
lemma x ys xys (Here ...)  = ...
lemma x ys xys (There ...) = ...

{-

  lemma : ∀ {m ns mns}
        → m ∪ ns ≡ mns → m <> sum ns ≡ sum mns
  lemma here = refl
  lemma {m} {n ∷ ns} (there p)
    rewrite sym (<>-assoc m n (sum ns))
          | <>-comm m n
          | <>-assoc n m (sum ns)
          | lemma p = refl

-}
