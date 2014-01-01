module State0 where

import State

{-@ fresh :: ST <{\v -> (v >= 0)}, {\xx v -> ((xx>=0) && (v>=0))}> Int Int @-}
fresh :: ST Int Int
fresh = S (\n -> (n, n+1))

{-@ incr4' :: ST <{\v -> (v>=0)}, {\xxxx v -> ((v>=0) && (xxxx>=0))}> Int Int @-}
incr4' :: ST Int Int
incr4' = fresh `bindST` returnST
