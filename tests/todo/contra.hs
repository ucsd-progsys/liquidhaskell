{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}

module Foo () where

import Language.Haskell.Liquid.Prelude (liquidAssert)
import Data.IORef

{-@ type Upto N = {v:Nat | v < N} @-} 


{-@ bob :: Nat -> IO () @-}
bob n = do
  t <- newIO (n+1) (\_ -> 0)
  setIO t 0 100
  r <- getIO t 0
  liquidAssert (r == 0) $ return ()

 
data IOArr a = IOA { size :: Int
                   , pntr :: IORef (Arr a)
                   }

data Arr a   = A { alen :: Int
                 , aval :: Int -> a
                 }



{-@ data IOArr a <p :: Int -> a -> Prop>
      = IOA { size :: Nat
            , pntr :: IORef ({v:Arr<p> a | alen v = size})
            }
  @-}


{-@ data Arr a <p :: Int -> a -> Prop>
             = A { alen :: Nat 
                 , aval :: i:Upto alen -> a<p i>
                 }
  @-}



{-@ newIO :: forall <p :: Int -> a -> Prop>.
               n:Nat -> (i:Upto n -> a<p i>) -> IO ({v: IOArr<p> a | size v = n})
  @-}
newIO :: Int -> (Int -> a) -> IO (IOArr a)
newIO n f = undefined

{-@ getIO :: forall <p :: Int -> a -> Prop>.
              a:IOArr<p> a -> i:Upto (size a) -> IO (a<p i>)
  @-}
getIO :: IOArr a -> Int-> IO a
getIO a@(IOA sz p) i = undefined

{-@ setIO :: forall <p :: Int -> a -> Prop>.
              a:IOArr<p> a -> i:Upto (size a) -> a<p i> -> IO ()
  @-}
setIO :: IOArr a -> Int -> a -> IO ()
setIO a@(IOA sz p) i v = undefined

