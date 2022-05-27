{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE CPP
           , ForeignFunctionInterface
           , GeneralizedNewtypeDeriving
           , NoImplicitPrelude
           , RecordWildCards
           , BangPatterns
  #-}

module GHC.Event.KQueue
    (
      new
    , available
    ) where

import qualified GHC.Event.Internal as E

#include "EventConfig.h"
#if !defined(HAVE_KQUEUE)
import GHC.Base

new :: IO E.Backend
new = error "KQueue back end not implemented for this platform"

available :: Bool
available = False
{-# INLINE available #-}
#else

import Control.Concurrent.MVar (MVar, newMVar, swapMVar, withMVar)
import Control.Monad (when, unless)
import Data.Bits (Bits(..))
import Data.Word (Word16, Word32)
import Foreign.C.Error (throwErrnoIfMinus1)
import Foreign.C.Types
import Foreign.Marshal.Alloc (alloca)
import Foreign.Ptr (Ptr, nullPtr)
import Foreign.Storable (Storable(..))
import GHC.Base
import GHC.Enum (toEnum)
import GHC.Err (undefined)
import GHC.Num (Num(..))
import GHC.Real (ceiling, floor, fromIntegral)
import GHC.Show (Show(show))
import GHC.Event.Internal (Timeout(..))
import System.Posix.Internals (c_close)
import System.Posix.Types (Fd(..))
import qualified GHC.Event.Array as A

#if defined(HAVE_KEVENT64)
import Data.Int (Int64)
import Data.Word (Word64)
#endif

#include <sys/types.h>
#include <sys/event.h>
#include <sys/time.h>

-- Handle brokenness on some BSD variants, notably OS X up to at least
-- 10.6.  If NOTE_EOF isn't available, we have no way to receive a
-- notification from the kernel when we reach EOF on a plain file.
#ifndef NOTE_EOF
# define NOTE_EOF 0
#endif

available :: Bool
available = True
{-# INLINE available #-}

------------------------------------------------------------------------
-- Exported interface

data EventQueue = EventQueue {
      eqFd       :: {-# UNPACK #-} !QueueFd
    , eqChanges  :: {-# UNPACK #-} !(MVar (A.Array Event))
    , eqEvents   :: {-# UNPACK #-} !(A.Array Event)
    }

new :: IO E.Backend
new = do
  qfd <- kqueue
  changesArr <- A.empty
  changes <- newMVar changesArr 
  events <- A.new 64
  let !be = E.backend poll modifyFd delete (EventQueue qfd changes events)
  return be

delete :: EventQueue -> IO ()
delete q = do
  _ <- c_close . fromQueueFd . eqFd $ q
  return ()

modifyFd :: EventQueue -> Fd -> E.Event -> E.Event -> IO ()
modifyFd q fd oevt nevt = withMVar (eqChanges q) $ \ch -> do
  let addChange filt flag = A.snoc ch $ event fd filt flag noteEOF
  when (oevt `E.eventIs` E.evtRead)  $ addChange filterRead flagDelete
  when (oevt `E.eventIs` E.evtWrite) $ addChange filterWrite flagDelete
  when (nevt `E.eventIs` E.evtRead)  $ addChange filterRead flagAdd
  when (nevt `E.eventIs` E.evtWrite) $ addChange filterWrite flagAdd

poll :: EventQueue
     -> Timeout
     -> (Fd -> E.Event -> IO ())
     -> IO ()
poll EventQueue{..} tout f = do
    changesArr <- A.empty
    changes <- swapMVar eqChanges changesArr
    changesLen <- A.length changes
    len <- A.length eqEvents
    when (changesLen > len) $ A.ensureCapacity eqEvents (2 * changesLen)
    n <- A.useAsPtr changes $ \changesPtr chLen ->
           A.unsafeLoad eqEvents $ \evPtr evCap ->
             withTimeSpec (fromTimeout tout) $
               kevent eqFd changesPtr chLen evPtr evCap

    unless (n == 0) $ do
        cap <- A.capacity eqEvents
        when (n == cap) $ A.ensureCapacity eqEvents (2 * cap)
        A.forM_ eqEvents $ \e -> f (fromIntegral (ident e)) (toEvent (filter e))

------------------------------------------------------------------------
-- FFI binding

newtype QueueFd = QueueFd {
      fromQueueFd :: CInt
    } deriving (Eq, Show)

#if defined(HAVE_KEVENT64)
data Event = KEvent64 {
      ident  :: {-# UNPACK #-} !Word64
    , filter :: {-# UNPACK #-} !Filter
    , flags  :: {-# UNPACK #-} !Flag
    , fflags :: {-# UNPACK #-} !FFlag
    , data_  :: {-# UNPACK #-} !Int64
    , udata  :: {-# UNPACK #-} !Word64
    , ext0   :: {-# UNPACK #-} !Word64
    , ext1   :: {-# UNPACK #-} !Word64
    } deriving Show

event :: Fd -> Filter -> Flag -> FFlag -> Event
event fd filt flag fflag = KEvent64 (fromIntegral fd) filt flag fflag 0 0 0 0

instance Storable Event where
    sizeOf _ = #size struct kevent64_s
    alignment _ = alignment (undefined :: CInt)

    peek ptr = do
        ident'  <- #{peek struct kevent64_s, ident} ptr
        filter' <- #{peek struct kevent64_s, filter} ptr
        flags'  <- #{peek struct kevent64_s, flags} ptr
        fflags' <- #{peek struct kevent64_s, fflags} ptr
        data'   <- #{peek struct kevent64_s, data} ptr
        udata'  <- #{peek struct kevent64_s, udata} ptr
        ext0'   <- #{peek struct kevent64_s, ext[0]} ptr
        ext1'   <- #{peek struct kevent64_s, ext[1]} ptr
        let !ev = KEvent64 ident' (Filter filter') (Flag flags') fflags' data'
                           udata' ext0' ext1'
        return ev

    poke ptr ev = do
        #{poke struct kevent64_s, ident} ptr (ident ev)
        #{poke struct kevent64_s, filter} ptr (filter ev)
        #{poke struct kevent64_s, flags} ptr (flags ev)
        #{poke struct kevent64_s, fflags} ptr (fflags ev)
        #{poke struct kevent64_s, data} ptr (data_ ev)
        #{poke struct kevent64_s, udata} ptr (udata ev)
        #{poke struct kevent64_s, ext[0]} ptr (ext0 ev)
        #{poke struct kevent64_s, ext[1]} ptr (ext1 ev)
#else
data Event = KEvent {
      ident  :: {-# UNPACK #-} !CUIntPtr
    , filter :: {-# UNPACK #-} !Filter
    , flags  :: {-# UNPACK #-} !Flag
    , fflags :: {-# UNPACK #-} !FFlag
    , data_  :: {-# UNPACK #-} !CIntPtr
    , udata  :: {-# UNPACK #-} !(Ptr ())
    } deriving Show

event :: Fd -> Filter -> Flag -> FFlag -> Event
event fd filt flag fflag = KEvent (fromIntegral fd) filt flag fflag 0 nullPtr

instance Storable Event where
    sizeOf _ = #size struct kevent
    alignment _ = alignment (undefined :: CInt)

    peek ptr = do
        ident'  <- #{peek struct kevent, ident} ptr
        filter' <- #{peek struct kevent, filter} ptr
        flags'  <- #{peek struct kevent, flags} ptr
        fflags' <- #{peek struct kevent, fflags} ptr
        data'   <- #{peek struct kevent, data} ptr
        udata'  <- #{peek struct kevent, udata} ptr
        let !ev = KEvent ident' (Filter filter') (Flag flags') fflags' data'
                         udata'
        return ev

    poke ptr ev = do
        #{poke struct kevent, ident} ptr (ident ev)
        #{poke struct kevent, filter} ptr (filter ev)
        #{poke struct kevent, flags} ptr (flags ev)
        #{poke struct kevent, fflags} ptr (fflags ev)
        #{poke struct kevent, data} ptr (data_ ev)
        #{poke struct kevent, udata} ptr (udata ev)
#endif

newtype FFlag = FFlag Word32
    deriving (Eq, Show, Storable)

#{enum FFlag, FFlag
 , noteEOF = NOTE_EOF
 }

newtype Flag = Flag Word16
    deriving (Eq, Show, Storable)

#{enum Flag, Flag
 , flagAdd     = EV_ADD
 , flagDelete  = EV_DELETE
 }

newtype Filter = Filter Word16
    deriving (Bits, Eq, Num, Show, Storable)

#{enum Filter, Filter
 , filterRead   = EVFILT_READ
 , filterWrite  = EVFILT_WRITE
 }

data TimeSpec = TimeSpec {
      tv_sec  :: {-# UNPACK #-} !CTime
    , tv_nsec :: {-# UNPACK #-} !CLong
    }

instance Storable TimeSpec where
    sizeOf _ = #size struct timespec
    alignment _ = alignment (undefined :: CInt)

    peek ptr = do
        tv_sec'  <- #{peek struct timespec, tv_sec} ptr
        tv_nsec' <- #{peek struct timespec, tv_nsec} ptr
        let !ts = TimeSpec tv_sec' tv_nsec'
        return ts

    poke ptr ts = do
        #{poke struct timespec, tv_sec} ptr (tv_sec ts)
        #{poke struct timespec, tv_nsec} ptr (tv_nsec ts)

kqueue :: IO QueueFd
kqueue = QueueFd `fmap` throwErrnoIfMinus1 "kqueue" c_kqueue

-- TODO: We cannot retry on EINTR as the timeout would be wrong.
-- Perhaps we should just return without calling any callbacks.
kevent :: QueueFd -> Ptr Event -> Int -> Ptr Event -> Int -> Ptr TimeSpec
       -> IO Int
kevent k chs chlen evs evlen ts
    = fmap fromIntegral $ E.throwErrnoIfMinus1NoRetry "kevent" $
#if defined(HAVE_KEVENT64)
      c_kevent64 k chs (fromIntegral chlen) evs (fromIntegral evlen) 0 ts
#else
      c_kevent k chs (fromIntegral chlen) evs (fromIntegral evlen) ts
#endif

withTimeSpec :: TimeSpec -> (Ptr TimeSpec -> IO a) -> IO a
withTimeSpec ts f =
    if tv_sec ts < 0 then
        f nullPtr
      else
        alloca $ \ptr -> poke ptr ts >> f ptr

fromTimeout :: Timeout -> TimeSpec
fromTimeout Forever     = TimeSpec (-1) (-1)
fromTimeout (Timeout s) = TimeSpec (toEnum sec) (toEnum nanosec)
  where
    sec :: Int
    sec     = floor s

    nanosec :: Int
    nanosec = ceiling $ (s - fromIntegral sec) * 1000000000

toEvent :: Filter -> E.Event
toEvent (Filter f)
    | f == (#const EVFILT_READ) = E.evtRead
    | f == (#const EVFILT_WRITE) = E.evtWrite
    | otherwise = error $ "toEvent: unknown filter " ++ show f

foreign import ccall unsafe "kqueue"
    c_kqueue :: IO CInt

#if defined(HAVE_KEVENT64)
foreign import ccall safe "kevent64"
    c_kevent64 :: QueueFd -> Ptr Event -> CInt -> Ptr Event -> CInt -> CUInt
               -> Ptr TimeSpec -> IO CInt
#elif defined(HAVE_KEVENT)
foreign import ccall safe "kevent"
    c_kevent :: QueueFd -> Ptr Event -> CInt -> Ptr Event -> CInt
             -> Ptr TimeSpec -> IO CInt
#else
#error no kevent system call available!?
#endif

#endif /* defined(HAVE_KQUEUE) */

