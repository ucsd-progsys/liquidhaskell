module Records where


import GHC.CString  -- This import interprets Strings as constants!

import DataBase 

data Value = I Int

{-@ safe   :: {v:Dict <{\v -> v == foo}, {\x y -> true}> String Value | listElts (ddom v) = (Set_sng foo)} @-}
safe :: Dict String Value
safe = ("foo" := I 8) += empty