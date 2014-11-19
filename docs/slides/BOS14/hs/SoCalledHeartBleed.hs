module HeartBleed where

import Data.ByteString.Char8  (pack, unpack) 
import Data.ByteString.Unsafe (unsafeTake)

heartBleed s n = s'
  where 
    b          = pack s         
    b'         = unsafeTake n b
    s'         = unpack b'

-- > let ex = "Ranjit Loves Burritos"
    
-- > heartBleed ex 1
--   "R"
    
-- > heartBleed ex 6
-- > "Ranjit"

-- > heartBleed ex 10
-- > "Ranjit Lov"
    
-- > heartBleed ex 30
-- > "Ranjit Loves Burritos\NUL\NUL\NUL\201\&1j\DC3\SOH\NUL"
