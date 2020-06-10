module spec Foreign.Ptr where

import GHC.Ptr

invariant {v:Foreign.Ptr.Ptr a | 0 <= plen  v }
invariant {v:Foreign.Ptr.Ptr a | 0 <= pbase v }

