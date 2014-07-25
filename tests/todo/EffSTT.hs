module EffSTT (

  -- * Basic STT type and instances
    STT
  , Ptr
    
  -- * Monadic operators
  , ret
  , bind

  -- * Create a reference
  , newPtr
 
  -- * Read a reference
  , readPtr

  -- * Write a reference
  , writePtr
    
  )where

import qualified Data.Map as M

type State  = M.Map Int Int
newtype Ptr = Ptr Int
data STT a  = STT (State -> (a, State)) 

----------------------------------------------------------------
-- | Accessing State via Ptr
----------------------------------------------------------------

{-@ newPtr :: forall <H :: HProp>.
                 n:Int
              -> STT <{H}, {\l -> H * l := n}> Ptr
  @-} 
newPtr   :: Int -> STT Ptr
newPtr n = STT $ \m0 ->
  let p  = M.size m0
      m1 = M.insert p n m0
  in
      (Ptr p, m1)

{-@ readPtr :: forall <p :: Int -> Prop, H :: HProp>.
                  l:Ptr
               -> STT <{H * l := Int<p>}, {\_ -> H * l := Int<p>}> Int<p>
  @-}
readPtr         :: Ptr -> STT Int
readPtr (Ptr p) = STT $ \m0 ->
  (M.findWithDefault (error "readPtr DIES") p m0, m0)


{-@ writePtr :: forall <p :: Int -> Prop, H :: HProp>.
                   l:Ptr
                -> Int<p>
                -> STT <{H * l := Int}, {\_ -> H * l := Int<p>}> () 
  @-} 
writePtr :: Ptr -> Int -> STT () 
writePtr (Ptr p) n = STT $ \m0 ->
  ((), M.insert p n m0)

----------------------------------------------------------------
-- | Monad instance for STT
----------------------------------------------------------------

instance Monad STT where
  return = ret
  (>>=)  = bind

ret   :: a -> STT a
ret x = STT (\s0 -> (x, s0))

bind :: STT a -> (a -> STT b) -> STT b
bind (STT f) k = STT $ \s0 ->
  let (x, s1) = f s0
      STT fk  = k x
  in
      fk s1

----------------------------------------------------------------
