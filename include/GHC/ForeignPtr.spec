module spec GHC.ForeignPtr where

import Foreign.ForeignPtr

mallocPlainForeignPtrBytes :: n:{v:GHC.Types.Int  | v >= 0 } -> (IO (ForeignPtrN a n))

