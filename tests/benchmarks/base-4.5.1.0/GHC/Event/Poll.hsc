{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE CPP
           , ForeignFunctionInterface
           , GeneralizedNewtypeDeriving
           , NoImplicitPrelude
           , BangPatterns
  #-}

module GHC.Event.Poll
    (
      new
    , available
    ) where

#include "EventConfig.h"

#if !defined(HAVE_POLL_H)
import GHC.Base

new :: IO E.Backend
new = error "Poll back end not implemented for this platform"

available :: Bool
available = False
{-# INLINE available #-}
#else
#include <poll.h>

import Control.Concurrent.MVar (MVar, newMVar, swapMVar)
import Control.Monad ((=<<), liftM, liftM2, unless)
import Data.Bits (Bits, (.|.), (.&.))
import Data.Maybe (Maybe(..))
import Data.Monoid (Monoid(..))
import Foreign.C.Types (CInt(..), CShort(..), CULong(..))
import Foreign.Ptr (Ptr)
import Foreign.Storable (Storable(..))
import GHC.Base
import GHC.Conc.Sync (withMVar)
import GHC.Err (undefined)
import GHC.Num (Num(..))
import GHC.Real (ceiling, fromIntegral)
import GHC.Show (Show)
import System.Posix.Types (Fd(..))

import qualified GHC.Event.Array as A
import qualified GHC.Event.Internal as E

available :: Bool
available = True
{-# INLINE available #-}

data Poll = Poll {
      pollChanges :: {-# UNPACK #-} !(MVar (A.Array PollFd))
    , pollFd      :: {-# UNPACK #-} !(A.Array PollFd)
    }

new :: IO E.Backend
new = E.backend poll modifyFd (\_ -> return ()) `liftM`
      liftM2 Poll (newMVar =<< A.empty) A.empty

modifyFd :: Poll -> Fd -> E.Event -> E.Event -> IO ()
modifyFd p fd oevt nevt =
  withMVar (pollChanges p) $ \ary ->
    A.snoc ary $ PollFd fd (fromEvent nevt) (fromEvent oevt)

reworkFd :: Poll -> PollFd -> IO ()
reworkFd p (PollFd fd npevt opevt) = do
  let ary = pollFd p
  if opevt == 0
    then A.snoc ary $ PollFd fd npevt 0
    else do
      found <- A.findIndex ((== fd) . pfdFd) ary
      case found of
        Nothing        -> error "reworkFd: event not found"
        Just (i,_)
          | npevt /= 0 -> A.unsafeWrite ary i $ PollFd fd npevt 0
          | otherwise  -> A.removeAt ary i

poll :: Poll
     -> E.Timeout
     -> (Fd -> E.Event -> IO ())
     -> IO ()
poll p tout f = do
  let a = pollFd p
  mods <- swapMVar (pollChanges p) =<< A.empty
  A.forM_ mods (reworkFd p)
  n <- A.useAsPtr a $ \ptr len -> E.throwErrnoIfMinus1NoRetry "c_poll" $
         c_poll ptr (fromIntegral len) (fromIntegral (fromTimeout tout))
  unless (n == 0) $ do
    A.loop a 0 $ \i e -> do
      let r = pfdRevents e
      if r /= 0
        then do f (pfdFd e) (toEvent r)
                let i' = i + 1
                return (i', i' == n)
        else return (i, True)

fromTimeout :: E.Timeout -> Int
fromTimeout E.Forever     = -1
fromTimeout (E.Timeout s) = ceiling $ 1000 * s

data PollFd = PollFd {
      pfdFd      :: {-# UNPACK #-} !Fd
    , pfdEvents  :: {-# UNPACK #-} !Event
    , pfdRevents :: {-# UNPACK #-} !Event
    } deriving (Show)

newtype Event = Event CShort
    deriving (Eq, Show, Num, Storable, Bits)

-- We have to duplicate the whole enum like this in order for the
-- hsc2hs cross-compilation mode to work
#ifdef POLLRDHUP
#{enum Event, Event
 , pollIn    = POLLIN
 , pollOut   = POLLOUT
 , pollRdHup = POLLRDHUP
 , pollErr   = POLLERR
 , pollHup   = POLLHUP
 }
#else
#{enum Event, Event
 , pollIn    = POLLIN
 , pollOut   = POLLOUT
 , pollErr   = POLLERR
 , pollHup   = POLLHUP
 }
#endif

fromEvent :: E.Event -> Event
fromEvent e = remap E.evtRead  pollIn .|.
              remap E.evtWrite pollOut
  where remap evt to
            | e `E.eventIs` evt = to
            | otherwise         = 0

toEvent :: Event -> E.Event
toEvent e = remap (pollIn .|. pollErr .|. pollHup)  E.evtRead `mappend`
            remap (pollOut .|. pollErr .|. pollHup) E.evtWrite
  where remap evt to
            | e .&. evt /= 0 = to
            | otherwise      = mempty

instance Storable PollFd where
    sizeOf _    = #size struct pollfd
    alignment _ = alignment (undefined :: CInt)

    peek ptr = do
      fd <- #{peek struct pollfd, fd} ptr
      events <- #{peek struct pollfd, events} ptr
      revents <- #{peek struct pollfd, revents} ptr
      let !pollFd' = PollFd fd events revents
      return pollFd'

    poke ptr p = do
      #{poke struct pollfd, fd} ptr (pfdFd p)
      #{poke struct pollfd, events} ptr (pfdEvents p)
      #{poke struct pollfd, revents} ptr (pfdRevents p)

foreign import ccall safe "poll.h poll"
    c_poll :: Ptr PollFd -> CULong -> CInt -> IO CInt

#endif /* defined(HAVE_POLL_H) */
