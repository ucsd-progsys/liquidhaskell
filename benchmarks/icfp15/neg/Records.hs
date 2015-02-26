module Records where


import GHC.CString  -- This import interprets Strings as constants!

import DataBase 

data Value = I Int


{-@ rec   :: {v:Dict <{\v -> v == bar}, {\x y -> true}> String Value | listElts (ddom v) = (Set_sng foo)} @-}
rec :: Dict String Value
rec = ("foo" := I 8) += empty


unsafe :: Dict String Value
unsafe = ("bar" := I 8) += empty