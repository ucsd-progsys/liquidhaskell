module RIO where

import Prelude hiding (read)

{-@ data FIO a <pre :: World -> Prop, post :: World -> a -> World -> Prop> 
  = FIO (rs :: (x:World<pre> -> (a, World)<\w -> {v:World<post x w> | true}>))
  @-}
data FIO a  = FIO {runState :: World -> (a, World)}

{-@ runState :: forall <pre :: World -> Prop, post :: World -> a -> World -> Prop>. 
                FIO <pre, post> a -> x:World<pre> -> (a, World)<\w -> {v:World<post x w> | true}> @-}

data World  = W


-- | forall m k v k'. sel (upd m k v) k' = if (k == k') then v else sel m k'

{-@ measure sel :: World -> FilePath -> Int          @-}
{-@ measure upd :: World -> FilePath -> Int -> World @-}


{-@ open :: fp:FilePath -> FIO <{\w0 -> true}, {\w0 r w1 -> w1 = w0  && sel w0 fp = 1}> () @-}
open :: FilePath -> FIO () 
open = undefined

{-@ read :: fp:FilePath -> FIO <{\w0 -> sel w0 fp = 1}, {\w0 r w1 -> w1 = w0}> String @-}
read :: FilePath -> FIO String
read = undefined

--------------------------


{-@
bind :: forall < pre   :: World -> Prop 
               , pre2  :: World -> Prop 
               , p     :: a -> Prop
               , post1 :: World -> a -> World -> Prop
               , post2 :: World -> b -> World -> Prop
               , post :: World -> b -> World -> Prop>.
       {w:World<pre> -> x:a -> World<post1 w x> -> World<pre2>}        
       {w:World<pre> -> y:a -> w2:World<post1 w y> -> x:b -> World<post2 w2 x> -> World<post w x>}        
       FIO <pre, post1> a
    -> (a -> FIO <pre2, post2> b)
    -> FIO <pre, post> b 

  @-}
bind :: FIO a -> (a -> FIO b) -> FIO b
bind (FIO g) f = FIO (\x -> case g x of {(y, s) -> (runState (f y)) s})    


-- is the precondition true or p?
{-@ ret :: forall <p :: World -> Prop>.
           x:a -> FIO <p, {\w0 y w1 -> w0 == w1 && y == x }> a @-}
ret :: a -> FIO a
ret w      = FIO $ \x -> (w, x)


ok1 f = open f

{-@ fail1 :: FilePath -> FIO String @-}
fail1 :: FilePath -> FIO String
fail1 f   = read f


ok2 f = open f `bind` \_ -> read f

instance Monad FIO where

{-@ instance Monad FIO where
 >>= :: forall < pre   :: World -> Prop 
               , pre2  :: World -> Prop 
               , p     :: a -> Prop
               , post1 :: World -> a -> World -> Prop
               , post2 :: World -> b -> World -> Prop
               , post :: World -> b -> World -> Prop>.
       {w:World<pre> -> x:a -> World<post1 w x> -> World<pre2>}        
       {w:World<pre> -> y:a -> w2:World<post1 w y> -> x:b -> World<post2 w2 x> -> World<post w x>}        
       FIO <pre, post1> a
    -> (a -> FIO <pre2, post2> b)
    -> FIO <pre, post> b ;
 >>  :: forall < pre   :: World -> Prop 
               , pre2  :: World -> Prop 
               , p     :: a -> Prop
               , post1 :: World -> a -> World -> Prop
               , post2 :: World -> b -> World -> Prop
               , post :: World -> b -> World -> Prop>.
       {w:World<pre> -> x:a -> World<post1 w x> -> World<pre2>}        
       {w:World<pre> -> y:a -> w2:World<post1 w y> -> x:b -> World<post2 w2 x> -> World<post w x>}        
       FIO <pre, post1> a
    -> FIO <pre2, post2> b
    -> FIO <pre, post> b ;
 return :: forall <p :: World -> Prop>.
           x:a -> FIO <p, {\w0 y w1 -> w0 == w1 && y == x }> a
  @-}  
  (FIO g) >>= f = FIO $ \x -> case g x of {(y, s) -> (runState (f y)) s} 
  (FIO g) >>  f = FIO $ \x -> case g x of {(y, s) -> (runState f    ) s}    
  return w      = FIO $ \x -> (w, x)
  fail          = error


{-@ ok3   :: FilePath -> FIO String @-}
ok3 f = do open f
           read f

