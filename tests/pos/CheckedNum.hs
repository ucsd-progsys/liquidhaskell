module CheckedNum where

-- Hiding numeric operations, because they get by default translated to SMT equivalent
import Prelude hiding (Num(..))

import qualified Prelude as Prelude 

class CheckedNum a where 
  (+) :: a -> a -> a 
  (-) :: a -> a -> a 

{-@ predicate BoundInt X = 0 < X + 10000 && X < 10000 @-}

instance CheckedNum Int where
{-@ instance CheckedNum Int where 
      - :: x:Int -> y:{v:Int | BoundInt (x - v)} -> {v: Int | v == x - y} ;  
      + :: x:Int -> y:{v:Int | BoundInt (x + v)} -> {v: Int | v == x + y} 
  @-}
	x - y = (Prelude.-) x y  

	x + y = (Prelude.+) x y  



