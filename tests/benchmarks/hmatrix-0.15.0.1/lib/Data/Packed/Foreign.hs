{-# LANGUAGE MagicHash, UnboxedTuples #-}
-- | FFI and hmatrix helpers.
--
-- Sample usage, to upload a perspective matrix to a shader.
--
-- @ glUniformMatrix4fv 0 1 (fromIntegral gl_TRUE) \`appMatrix\` perspective 0.01 100 (pi\/2) (4\/3) 
-- @
--
module Data.Packed.Foreign 
    ( app
    , appVector, appVectorLen
    , appMatrix, appMatrixLen, appMatrixRaw, appMatrixRawLen
    , unsafeMatrixToVector, unsafeMatrixToForeignPtr
    ) where
import Data.Packed.Internal
import qualified Data.Vector.Storable as S
import Foreign (Ptr, ForeignPtr, Storable)
import Foreign.C.Types (CInt)
import GHC.Base (IO(..), realWorld#)

{-# INLINE unsafeInlinePerformIO #-}
-- | If we use unsafePerformIO, it may not get inlined, so in a function that returns IO (which are all safe uses of app* in this module), there would be
-- unecessary calls to unsafePerformIO or its internals.
unsafeInlinePerformIO :: IO a -> a
unsafeInlinePerformIO (IO f) = case f realWorld# of
    (# _, x #) -> x

{-# INLINE app #-}
-- | Only useful since it is left associated with a precedence of 1, unlike 'Prelude.$', which is right associative.
-- e.g.
--
-- @
-- someFunction
--     \`appMatrixLen\` m
--     \`appVectorLen\` v
--     \`app\` other
--     \`app\` arguments
--     \`app\` go here
-- @
--
-- One could also write:
--
-- @
-- (someFunction 
--     \`appMatrixLen\` m
--     \`appVectorLen\` v) 
--     other 
--     arguments 
--     (go here)
-- @
--
app :: (a -> b) -> a -> b
app f = f

{-# INLINE appVector #-}
appVector :: Storable a => (Ptr a -> b) -> Vector a -> b
appVector f x = unsafeInlinePerformIO (S.unsafeWith x (return . f))

{-# INLINE appVectorLen #-}
appVectorLen :: Storable a => (CInt -> Ptr a -> b) -> Vector a -> b
appVectorLen f x = unsafeInlinePerformIO (S.unsafeWith x (return . f (fromIntegral (S.length x))))

{-# INLINE appMatrix #-}
appMatrix :: Element a => (Ptr a -> b) -> Matrix a -> b
appMatrix f x = unsafeInlinePerformIO (S.unsafeWith (flatten x) (return . f))

{-# INLINE appMatrixLen #-}
appMatrixLen :: Element a => (CInt -> CInt -> Ptr a -> b) -> Matrix a -> b
appMatrixLen f x = unsafeInlinePerformIO (S.unsafeWith (flatten x) (return . f r c))
  where
    r = fromIntegral (rows x)
    c = fromIntegral (cols x)

{-# INLINE appMatrixRaw #-}
appMatrixRaw :: Storable a => (Ptr a -> b) -> Matrix a -> b
appMatrixRaw f x = unsafeInlinePerformIO (S.unsafeWith (xdat x) (return . f))

{-# INLINE appMatrixRawLen #-}
appMatrixRawLen :: Element a => (CInt -> CInt -> Ptr a -> b) -> Matrix a -> b
appMatrixRawLen f x = unsafeInlinePerformIO (S.unsafeWith (xdat x) (return . f r c))
  where
    r = fromIntegral (rows x)
    c = fromIntegral (cols x)

infixl 1 `app`
infixl 1 `appVector`
infixl 1 `appMatrix`
infixl 1 `appMatrixRaw`

{-# INLINE unsafeMatrixToVector #-}
-- | This will disregard the order of the matrix, and simply return it as-is. 
-- If the order of the matrix is RowMajor, this function is identical to 'flatten'.
unsafeMatrixToVector :: Matrix a -> Vector a
unsafeMatrixToVector = xdat

{-# INLINE unsafeMatrixToForeignPtr #-}
unsafeMatrixToForeignPtr :: Storable a => Matrix a -> (ForeignPtr a, Int)
unsafeMatrixToForeignPtr m = S.unsafeToForeignPtr0 (xdat m)

