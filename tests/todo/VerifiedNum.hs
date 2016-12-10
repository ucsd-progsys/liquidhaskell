module VerifiedNum where

-- Hiding numeric operations, because they get by default translated to SMT equivalent
import Prelude hiding (Num(..))

import qualified Prelude as Prelude 

class VerifiedNum a where 
  (+) :: a -> a -> a 
  (-) :: a -> a -> a 

{-@ predicate BoundInt X = 0 < X + 10000 && X < 10000 @-}

{-@ type OkInt N = {v:Int | BoundInt N => v == N} @-}

{-@ type ValidInt = {v:Int | BoundInt v} @-}


instance VerifiedNum Int where
{-@ instance VerifiedNum Int where 
    + :: x:Int -> y:Int -> OkInt {x + y} 
  @-}
	x + y = (Prelude.+) x y  
{-@ instance VerifiedNum Int where 
    - :: x:Int -> y:Int -> OkInt {x - y} 
  @-}
	x - y = (Prelude.-) x y  




