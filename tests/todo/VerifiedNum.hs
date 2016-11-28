module VerifiedNum where

-- Hiding numeric operations, because they get by default translated to SMT equivalent
import Prelude hiding (Num(..))

import qualified Prelude as Prelude 

class VerifiedNum a where
	(+) :: a -> a -> a 


-- Say that + overflows at 10, 
-- when addition exceeds 10, then its result is undefined 

instance VerifiedNum Int where
{-@ instance VerifiedNum Int where 
  + :: x:Int -> y:Int -> {v:Int | (x + y < 10) => x + y = v} @-}
	x + y = (Prelude.+) x y  

-- 10 + 20 overflows, cannot reason about its result
{-@ overflow :: {v:Int | v == 30} @-}
overflow :: Int 
overflow = 10 + 20 

-- no overflow
{-@ safe :: {v:Int | v == 3} @-}
safe :: Int 
safe = 1 + 2
