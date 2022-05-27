{-# LANGUAGE Unsafe #-}
{-# LANGUAGE CPP
           , NoImplicitPrelude
           , BangPatterns
           , MagicHash
           , UnboxedTuples
  #-}
{-# OPTIONS_HADDOCK hide #-}
{-# LANGUAGE DeriveDataTypeable, StandaloneDeriving #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  GHC.ForeignPtr
-- Copyright   :  (c) The University of Glasgow, 1992-2003
-- License     :  see libraries/base/LICENSE
-- 
-- Maintainer  :  cvs-ghc@haskell.org
-- Stability   :  internal
-- Portability :  non-portable (GHC extensions)
--
-- GHC's implementation of the 'ForeignPtr' data type.
-- 
-----------------------------------------------------------------------------

-- #hide
module GHC.ForeignPtr
  (
        ForeignPtr(..),
        FinalizerPtr,
        FinalizerEnvPtr,
        newForeignPtr_,
        mallocForeignPtr,
        mallocPlainForeignPtr,
        mallocForeignPtrBytes,
        mallocPlainForeignPtrBytes,
        addForeignPtrFinalizer,
        addForeignPtrFinalizerEnv,
        touchForeignPtr,
        unsafeForeignPtrToPtr,
        castForeignPtr,
        newConcForeignPtr,
        addForeignPtrConcFinalizer,
        finalizeForeignPtr
  ) where

import Control.Monad    ( sequence_ )
import Foreign.Storable
import Data.Typeable

import GHC.Show
import GHC.List         ( null )
import GHC.Base
import GHC.IORef
import GHC.STRef        ( STRef(..) )
import GHC.Ptr          ( Ptr(..), FunPtr(..) )
import GHC.Err

#include "Typeable.h"

-- |The type 'ForeignPtr' represents references to objects that are
-- maintained in a foreign language, i.e., that are not part of the
-- data structures usually managed by the Haskell storage manager.
-- The essential difference between 'ForeignPtr's and vanilla memory
-- references of type @Ptr a@ is that the former may be associated
-- with /finalizers/. A finalizer is a routine that is invoked when
-- the Haskell storage manager detects that - within the Haskell heap
-- and stack - there are no more references left that are pointing to
-- the 'ForeignPtr'.  Typically, the finalizer will, then, invoke
-- routines in the foreign language that free the resources bound by
-- the foreign object.
--
-- The 'ForeignPtr' is parameterised in the same way as 'Ptr'.  The
-- type argument of 'ForeignPtr' should normally be an instance of
-- class 'Storable'.
--
data ForeignPtr a = ForeignPtr Addr# ForeignPtrContents
        -- we cache the Addr# in the ForeignPtr object, but attach
        -- the finalizer to the IORef (or the MutableByteArray# in
        -- the case of a MallocPtr).  The aim of the representation
        -- is to make withForeignPtr efficient; in fact, withForeignPtr
        -- should be just as efficient as unpacking a Ptr, and multiple
        -- withForeignPtrs can share an unpacked ForeignPtr.  Note
        -- that touchForeignPtr only has to touch the ForeignPtrContents
        -- object, because that ensures that whatever the finalizer is
        -- attached to is kept alive.

INSTANCE_TYPEABLE1(ForeignPtr,foreignPtrTc,"ForeignPtr")

data Finalizers
  = NoFinalizers
  | CFinalizers
  | HaskellFinalizers
    deriving Eq

data ForeignPtrContents
  = PlainForeignPtr !(IORef (Finalizers, [IO ()]))
  | MallocPtr      (MutableByteArray# RealWorld) !(IORef (Finalizers, [IO ()]))
  | PlainPtr       (MutableByteArray# RealWorld)

instance Eq (ForeignPtr a) where
    p == q  =  unsafeForeignPtrToPtr p == unsafeForeignPtrToPtr q

instance Ord (ForeignPtr a) where
    compare p q  =  compare (unsafeForeignPtrToPtr p) (unsafeForeignPtrToPtr q)

instance Show (ForeignPtr a) where
    showsPrec p f = showsPrec p (unsafeForeignPtrToPtr f)


-- |A finalizer is represented as a pointer to a foreign function that, at
-- finalisation time, gets as an argument a plain pointer variant of the
-- foreign pointer that the finalizer is associated with.
-- 
type FinalizerPtr a        = FunPtr (Ptr a -> IO ())
type FinalizerEnvPtr env a = FunPtr (Ptr env -> Ptr a -> IO ())

newConcForeignPtr :: Ptr a -> IO () -> IO (ForeignPtr a)
--
-- ^Turns a plain memory reference into a foreign object by
-- associating a finalizer - given by the monadic operation - with the
-- reference.  The storage manager will start the finalizer, in a
-- separate thread, some time after the last reference to the
-- @ForeignPtr@ is dropped.  There is no guarantee of promptness, and
-- in fact there is no guarantee that the finalizer will eventually
-- run at all.
--
-- Note that references from a finalizer do not necessarily prevent
-- another object from being finalized.  If A's finalizer refers to B
-- (perhaps using 'touchForeignPtr', then the only guarantee is that
-- B's finalizer will never be started before A's.  If both A and B
-- are unreachable, then both finalizers will start together.  See
-- 'touchForeignPtr' for more on finalizer ordering.
--
newConcForeignPtr p finalizer
  = do fObj <- newForeignPtr_ p
       addForeignPtrConcFinalizer fObj finalizer
       return fObj

mallocForeignPtr :: Storable a => IO (ForeignPtr a)
-- ^ Allocate some memory and return a 'ForeignPtr' to it.  The memory
-- will be released automatically when the 'ForeignPtr' is discarded.
--
-- 'mallocForeignPtr' is equivalent to
--
-- >    do { p <- malloc; newForeignPtr finalizerFree p }
-- 
-- although it may be implemented differently internally: you may not
-- assume that the memory returned by 'mallocForeignPtr' has been
-- allocated with 'Foreign.Marshal.Alloc.malloc'.
--
-- GHC notes: 'mallocForeignPtr' has a heavily optimised
-- implementation in GHC.  It uses pinned memory in the garbage
-- collected heap, so the 'ForeignPtr' does not require a finalizer to
-- free the memory.  Use of 'mallocForeignPtr' and associated
-- functions is strongly recommended in preference to 'newForeignPtr'
-- with a finalizer.
-- 
mallocForeignPtr = doMalloc undefined
  where doMalloc :: Storable b => b -> IO (ForeignPtr b)
        doMalloc a
          | I# size < 0 = error "mallocForeignPtr: size must be >= 0"
          | otherwise = do
          r <- newIORef (NoFinalizers, [])
          IO $ \s ->
            case newAlignedPinnedByteArray# size align s of { (# s', mbarr# #) ->
             (# s', ForeignPtr (byteArrayContents# (unsafeCoerce# mbarr#))
                               (MallocPtr mbarr# r) #)
            }
            where !(I# size)  = sizeOf a
                  !(I# align) = alignment a

-- | This function is similar to 'mallocForeignPtr', except that the
-- size of the memory required is given explicitly as a number of bytes.
mallocForeignPtrBytes :: Int -> IO (ForeignPtr a)
mallocForeignPtrBytes size | size < 0 =
  error "mallocForeignPtrBytes: size must be >= 0"
mallocForeignPtrBytes (I# size) = do 
  r <- newIORef (NoFinalizers, [])
  IO $ \s ->
     case newPinnedByteArray# size s      of { (# s', mbarr# #) ->
       (# s', ForeignPtr (byteArrayContents# (unsafeCoerce# mbarr#))
                         (MallocPtr mbarr# r) #)
     }

-- | Allocate some memory and return a 'ForeignPtr' to it.  The memory
-- will be released automatically when the 'ForeignPtr' is discarded.
--
-- GHC notes: 'mallocPlainForeignPtr' has a heavily optimised
-- implementation in GHC.  It uses pinned memory in the garbage
-- collected heap, as for mallocForeignPtr. Unlike mallocForeignPtr, a
-- ForeignPtr created with mallocPlainForeignPtr carries no finalizers.
-- It is not possible to add a finalizer to a ForeignPtr created with
-- mallocPlainForeignPtr. This is useful for ForeignPtrs that will live
-- only inside Haskell (such as those created for packed strings).
-- Attempts to add a finalizer to a ForeignPtr created this way, or to
-- finalize such a pointer, will throw an exception.
-- 
mallocPlainForeignPtr :: Storable a => IO (ForeignPtr a)
mallocPlainForeignPtr = doMalloc undefined
  where doMalloc :: Storable b => b -> IO (ForeignPtr b)
        doMalloc a
          | I# size < 0 = error "mallocForeignPtr: size must be >= 0"
          | otherwise = IO $ \s ->
            case newAlignedPinnedByteArray# size align s of { (# s', mbarr# #) ->
             (# s', ForeignPtr (byteArrayContents# (unsafeCoerce# mbarr#))
                               (PlainPtr mbarr#) #)
            }
            where !(I# size)  = sizeOf a
                  !(I# align) = alignment a

-- | This function is similar to 'mallocForeignPtrBytes', except that
-- the internally an optimised ForeignPtr representation with no
-- finalizer is used. Attempts to add a finalizer will cause an
-- exception to be thrown.
mallocPlainForeignPtrBytes :: Int -> IO (ForeignPtr a)
mallocPlainForeignPtrBytes size | size < 0 =
  error "mallocPlainForeignPtrBytes: size must be >= 0"
mallocPlainForeignPtrBytes (I# size) = IO $ \s ->
    case newPinnedByteArray# size s      of { (# s', mbarr# #) ->
       (# s', ForeignPtr (byteArrayContents# (unsafeCoerce# mbarr#))
                         (PlainPtr mbarr#) #)
     }

addForeignPtrFinalizer :: FinalizerPtr a -> ForeignPtr a -> IO ()
-- ^This function adds a finalizer to the given foreign object.  The
-- finalizer will run /before/ all other finalizers for the same
-- object which have already been registered.
addForeignPtrFinalizer (FunPtr fp) (ForeignPtr p c) = case c of
  PlainForeignPtr r -> f r >> return ()
  MallocPtr     _ r -> f r >> return ()
  _ -> error "GHC.ForeignPtr: attempt to add a finalizer to a plain pointer"
 where
    f r =
      noMixing CFinalizers r $
        IO $ \s ->
          case r of { IORef (STRef r#) ->
          case mkWeakForeignEnv# r# () fp p 0# nullAddr# s of { (# s1, w #) ->
          (# s1, finalizeForeign w #) }}

addForeignPtrFinalizerEnv ::
  FinalizerEnvPtr env a -> Ptr env -> ForeignPtr a -> IO ()
-- ^ Like 'addForeignPtrFinalizerEnv' but allows the finalizer to be
-- passed an additional environment parameter to be passed to the
-- finalizer.  The environment passed to the finalizer is fixed by the
-- second argument to 'addForeignPtrFinalizerEnv'
addForeignPtrFinalizerEnv (FunPtr fp) (Ptr ep) (ForeignPtr p c) = case c of
  PlainForeignPtr r -> f r >> return ()
  MallocPtr     _ r -> f r >> return ()
  _ -> error "GHC.ForeignPtr: attempt to add a finalizer to a plain pointer"
 where
    f r =
      noMixing CFinalizers r $
        IO $ \s ->
          case r of { IORef (STRef r#) ->
          case mkWeakForeignEnv# r# () fp p 1# ep s of { (# s1, w #) ->
          (# s1, finalizeForeign w #) }}

finalizeForeign :: Weak# () -> IO ()
finalizeForeign w = IO $ \s ->
  case finalizeWeak# w s of
    (# s1, 0#, _ #) -> (# s1, () #)
    (# s1, _ , f #) -> f s1

addForeignPtrConcFinalizer :: ForeignPtr a -> IO () -> IO ()
-- ^This function adds a finalizer to the given @ForeignPtr@.  The
-- finalizer will run /before/ all other finalizers for the same
-- object which have already been registered.
--
-- This is a variant of @addForeignPtrFinalizer@, where the finalizer
-- is an arbitrary @IO@ action.  When it is invoked, the finalizer
-- will run in a new thread.
--
-- NB. Be very careful with these finalizers.  One common trap is that
-- if a finalizer references another finalized value, it does not
-- prevent that value from being finalized.  In particular, 'Handle's
-- are finalized objects, so a finalizer should not refer to a 'Handle'
-- (including @stdout@, @stdin@ or @stderr@).
--
addForeignPtrConcFinalizer (ForeignPtr _ c) finalizer = 
  addForeignPtrConcFinalizer_ c finalizer

addForeignPtrConcFinalizer_ :: ForeignPtrContents -> IO () -> IO ()
addForeignPtrConcFinalizer_ (PlainForeignPtr r) finalizer = do
  noFinalizers <- noMixing HaskellFinalizers r (return finalizer)
  if noFinalizers
     then IO $ \s ->
              case r of { IORef (STRef r#) ->
              case mkWeak# r# () (foreignPtrFinalizer r) s of {  (# s1, _ #) ->
              (# s1, () #) }}
     else return ()
addForeignPtrConcFinalizer_ f@(MallocPtr fo r) finalizer = do
  noFinalizers <- noMixing HaskellFinalizers r (return finalizer)
  if noFinalizers
     then  IO $ \s -> 
               case mkWeak# fo () (do foreignPtrFinalizer r; touch f) s of
                  (# s1, _ #) -> (# s1, () #)
     else return ()

addForeignPtrConcFinalizer_ _ _ =
  error "GHC.ForeignPtr: attempt to add a finalizer to plain pointer"

noMixing ::
  Finalizers -> IORef (Finalizers, [IO ()]) -> IO (IO ()) -> IO Bool
noMixing ftype0 r mkF = do
  (ftype, fs) <- readIORef r
  if ftype /= NoFinalizers && ftype /= ftype0
     then error ("GHC.ForeignPtr: attempt to mix Haskell and C finalizers " ++
                 "in the same ForeignPtr")
     else do
       f <- mkF
       writeIORef r (ftype0, f : fs)
       return (null fs)

foreignPtrFinalizer :: IORef (Finalizers, [IO ()]) -> IO ()
foreignPtrFinalizer r = do (_, fs) <- readIORef r; sequence_ fs

newForeignPtr_ :: Ptr a -> IO (ForeignPtr a)
-- ^Turns a plain memory reference into a foreign pointer that may be
-- associated with finalizers by using 'addForeignPtrFinalizer'.
newForeignPtr_ (Ptr obj) =  do
  r <- newIORef (NoFinalizers, [])
  return (ForeignPtr obj (PlainForeignPtr r))

touchForeignPtr :: ForeignPtr a -> IO ()
-- ^This function ensures that the foreign object in
-- question is alive at the given place in the sequence of IO
-- actions. In particular 'Foreign.ForeignPtr.withForeignPtr'
-- does a 'touchForeignPtr' after it
-- executes the user action.
-- 
-- Note that this function should not be used to express dependencies
-- between finalizers on 'ForeignPtr's.  For example, if the finalizer
-- for a 'ForeignPtr' @F1@ calls 'touchForeignPtr' on a second
-- 'ForeignPtr' @F2@, then the only guarantee is that the finalizer
-- for @F2@ is never started before the finalizer for @F1@.  They
-- might be started together if for example both @F1@ and @F2@ are
-- otherwise unreachable, and in that case the scheduler might end up
-- running the finalizer for @F2@ first.
--
-- In general, it is not recommended to use finalizers on separate
-- objects with ordering constraints between them.  To express the
-- ordering robustly requires explicit synchronisation using @MVar@s
-- between the finalizers, but even then the runtime sometimes runs
-- multiple finalizers sequentially in a single thread (for
-- performance reasons), so synchronisation between finalizers could
-- result in artificial deadlock.  Another alternative is to use
-- explicit reference counting.
--
touchForeignPtr (ForeignPtr _ r) = touch r

touch :: ForeignPtrContents -> IO ()
touch r = IO $ \s -> case touch# r s of s' -> (# s', () #)

unsafeForeignPtrToPtr :: ForeignPtr a -> Ptr a
-- ^This function extracts the pointer component of a foreign
-- pointer.  This is a potentially dangerous operations, as if the
-- argument to 'unsafeForeignPtrToPtr' is the last usage
-- occurrence of the given foreign pointer, then its finalizer(s) will
-- be run, which potentially invalidates the plain pointer just
-- obtained.  Hence, 'touchForeignPtr' must be used
-- wherever it has to be guaranteed that the pointer lives on - i.e.,
-- has another usage occurrence.
--
-- To avoid subtle coding errors, hand written marshalling code
-- should preferably use 'Foreign.ForeignPtr.withForeignPtr' rather
-- than combinations of 'unsafeForeignPtrToPtr' and
-- 'touchForeignPtr'.  However, the latter routines
-- are occasionally preferred in tool generated marshalling code.
unsafeForeignPtrToPtr (ForeignPtr fo _) = Ptr fo

castForeignPtr :: ForeignPtr a -> ForeignPtr b
-- ^This function casts a 'ForeignPtr'
-- parameterised by one type into another type.
castForeignPtr f = unsafeCoerce# f

-- | Causes the finalizers associated with a foreign pointer to be run
-- immediately.
finalizeForeignPtr :: ForeignPtr a -> IO ()
finalizeForeignPtr (ForeignPtr _ (PlainPtr _)) = return () -- no effect
finalizeForeignPtr (ForeignPtr _ foreignPtr) = do
        (ftype, finalizers) <- readIORef refFinalizers
        sequence_ finalizers
        writeIORef refFinalizers (ftype, [])
        where
                refFinalizers = case foreignPtr of
                        (PlainForeignPtr ref) -> ref
                        (MallocPtr     _ ref) -> ref
                        PlainPtr _            ->
                            error "finalizeForeignPtr PlainPtr"

