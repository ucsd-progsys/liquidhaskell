module CImport where

import Foreign.Ptr              (Ptr, FunPtr, plusPtr)
import Data.Word                (Word8)
import Foreign.C.Types          (CInt(..), CSize(..), CULong(..))

foreign import ccall unsafe "string.h memchr" c_memchr
     :: Ptr Word8 -> CInt -> CSize -> IO (Ptr Word8)

