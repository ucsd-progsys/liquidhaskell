module StackSet () where

import Data.Set (Set(..)) 

data LL a = Nil | Cons { head :: a, tail :: LL a }

{-@ data LL a = Nil | Cons { head :: a 
                           , tail :: {v: LL a | not (Set_mem head (elts v))  } } 
  @-}

{-@ measure elts :: LL a -> (Set a) 
    elts (Nil)       = {v | (Set_emp v)}
    elts (Cons x xs) = {v | v = (Set_cup (Set_sng x) (elts xs)) }
  @-}

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



