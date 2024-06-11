{-@ LIQUID "--exact-data-cons" @-}
module B where

import A

data Exp = Lam Ty

-- Ibung:
-- 1. If we remove --exact-data-cons above, this example goes through
-- 2. Otherwise, LH complains about unknown type constructor 'A.Ty'

-- Interestingly, 
-- 1. if we put --exact-data-cons in A.hs and remove this one
--    we would still get the same error
-- 2. if we put --exact-data-cons in A.hs C.hs and remove this one
--    we would get illegal type specification for A.TInt
--
