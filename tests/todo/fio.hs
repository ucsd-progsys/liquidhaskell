module FIO where

import Prelude hiding (read)

{-@ data FIO a <pre :: World -> Prop, post :: World -> World -> a -> Prop> 
  = FOO (rs :: (x:World<pre> -> (World, a)<\w -> {v:a<post x w> | true}>))
  @-}
data FIO a  = FOO (World -> (World, a))

data World  = W


-- | forall m k v k'. sel (upd m k v) k' = if (k == k') then v else sel m k'

{-@ measure sel :: World -> FilePath -> Int          @-}
{-@ measure upd :: World -> FilePath -> Int -> World @-}


{-@ open :: fp:FilePath -> FIO <{\w0 -> true}, {\w0 w1 r -> w1 = w0  && sel w0 fp = 1}> () @-}
open :: FilePath -> FIO () 
open = undefined

{-@ read :: fp:FilePath -> FIO <{\w0 -> sel w0 fp = 1}, {\w0 w1 r -> w1 = w0}> String @-}
read :: FilePath -> FIO String
read = undefined

--------------------------


bind = undefined  -- TODO
ret  = undefined  -- TODO


ok1 f = open f

{-@ fail1 :: FilePath -> FIO String @-}
fail1 :: FilePath -> FIO String
fail1 f   = read f


{-
ok2 f = open f `bind` \_ -> read f

instance Monad FIO where
  (>>=)  = bind
  return = ret

{- ok3   :: FilePath -> FIO () @-}
ok3 f = do open f
           read f

-}

