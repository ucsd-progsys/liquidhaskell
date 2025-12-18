module FF17 where

import Language.Haskell.Liquid.FinField.FF17

{-@ thm1 :: { v : FF17 | v = val 6} -> { add v (val 7) == val 13 } @-}
thm1 :: FF17 -> ()
thm1 _ = ()

{-@ thm2 :: { v : FF17 | v = val 9} -> { add v (val 9) == val 1 } @-}
thm2 :: FF17 -> ()
thm2 _ = ()

{-@ thm3 :: { v : FF17 | v = val 3} -> { mul v (val 7) == val 4 } @-}
thm3 :: FF17 -> ()
thm3 _ = ()
