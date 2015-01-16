module FIO where

import Prelude hiding (read)

{-@ data FIO a <pre :: World -> Prop, post :: World -> World -> a -> Prop> 
  = FIO (rs :: (x:World<pre> -> (World, a)<\w -> {v:a<post x w> | true}>))
  @-}
data FIO a  = FIO {runState :: World -> (World, a)}

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

{-
bind :: forall < pref :: s -> Prop, postf :: s -> s -> Prop
              , pre  :: s -> Prop, postg :: s -> s -> Prop
              , post :: s -> s -> Prop
              , rg   :: s -> a -> Prop
              , rf   :: s -> b -> Prop
              , r    :: s -> b -> Prop
              , pref0 :: a -> Prop 
              >. 
       {x:s<pre> -> a<rg x> -> a<pref0>}      
       {x:s<pre> -> y:s<postg x> -> b<rf y> -> b<r x>}
       {xx:s<pre> -> w:s<postg xx> -> s<postf w> -> s<post xx>}
       {ww:s<pre> -> s<postg ww> -> s<pref>}
       (ST <pre, postg, rg> s a)
    -> (a<pref0> -> ST <pref, postf, rf> s b)
    -> (ST <pre, post, r> s b)
@-}

{-
bind :: 

  @-}
bind :: FIO a -> (a -> FIO b) -> FIO b
bind (FIO g) f = FIO (\x -> case g x of {(s, y) -> (runState (f y)) s})    

ret  = undefined  -- TODO


ok1 f = open f

{-@ fail1 :: FilePath -> FIO String @-}
fail1 :: FilePath -> FIO String
fail1 f   = read f



-- ok2 f = open f `bind` \_ -> read f

{-
instance Monad FIO where
  (>>=)  = bind
  return = ret

{- ok3   :: FilePath -> FIO () @-}
ok3 f = do open f
           read f

-}

