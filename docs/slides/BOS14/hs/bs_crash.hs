module BSCrash where

import Data.ByteString.Char8  as C
import Data.ByteString        as B
import Data.ByteString.Unsafe as U


heartBleed s n = s'
  where 
    b          = C.pack s         -- "Ranjit"
    b'         = U.unsafeTake n b -- 20
    s'         = C.unpack b'

-- > let ex = "Ranjit Loves Burritos"
    
-- > heartBleed ex 1
--   "R"
    
-- > heartBleed ex 6
-- > "Ranjit"

-- > heartBleed ex 10
-- > "Ranjit Lov"
    
-- > heartBleed ex 30
-- > "Ranjit Loves Burritos\NUL\NUL\NUL\201\&1j\DC3\SOH\NUL"
