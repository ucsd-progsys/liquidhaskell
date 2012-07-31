module Tx where

{-@ assert getHeads   :: xs:[{v:[a]| len(v) > 0}] -> {v:[a] | len(v) = len(xs)} @-}
getHeads xss = [ h | (h:_) <- xss]

{- The above requires we handle TAGS properly.
    the list comprehension versions require TAGs (see coreBinds)
        
        [ h | (h:_) <- xss]

    becomes

        foo []       = []
        foo (tmp:xss) = case tmp of
                         h:_     -> h : foo xss
                         DEFAULT -> foo xss
            
    and we need TAGS to relate len(v) > 0 and DEFAULT...
-}
-
