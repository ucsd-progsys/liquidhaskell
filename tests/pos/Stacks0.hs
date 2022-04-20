module Stacks0 () where

import qualified Data.Set as S -- (Set(..))

data LL a = Nil | Cons { headC :: a
                       , tailC :: LL a
                       }

{-@ data LL a = Nil | Cons { headC :: a
                           , tailC :: {v: LL a | not (Set_mem headC (elts v)) }
                           }
  @-}

{-@ measure elts @-} 
elts :: (Ord a) => LL a -> S.Set a
elts (Nil)       = S.empty
elts (Cons x xs) = S.union (S.singleton x) (elts xs)

{-@ predicate Disjoint X Y = (Set_emp (Set_cap (elts X) (elts Y))) @-}
{-@ predicate NotIn    X Y = not (Set_mem X (elts Y))              @-}

ll2 = Cons x0 (Cons x1 (Cons x2 Nil))
  where x0 :: Int
        x0  = 0
        x1  = 1
        x2  = 2

{-@ data Stack a = St { focus  :: a
                      , up     :: {vu: LL a | (NotIn focus vu) }
                      , down   :: {vd: LL a | ((NotIn focus vd) && (Disjoint up vd)) }
                      }
  @-}

data Stack a = St { focus  :: !a
                  , up     :: !(LL a)
                  , down   :: !(LL a)
                  }

{-@ fresh :: a -> Stack a @-}
fresh x = St x Nil Nil

{-@ moveUp :: Stack a -> Stack a @-}
moveUp (St x (Cons y ys) zs) = St y ys (Cons x zs)
moveUp s                     = s

{-@ moveDn :: Stack a -> Stack a @-}
moveDn (St x ys (Cons z zs)) = St z (Cons x ys) zs
moveDn s                     = s
