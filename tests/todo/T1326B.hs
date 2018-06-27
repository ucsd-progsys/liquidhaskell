{-@ LIQUID "--reflection"  @-}

module T1326B where

import T1326A 

data Program l = PHole | Pg {pTerm :: Term l }
