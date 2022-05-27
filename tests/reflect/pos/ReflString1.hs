
-- cf https://github.com/ucsd-progsys/liquidhaskell/issues/1044

{-@ LIQUID "--reflection" @-}

module ReflString1 where

data Vname = V String 

{-@ reflect xVar @-}
xVar :: Vname 
xVar = V "x"

{-@ reflect yVar @-}
yVar :: Vname 
yVar = V "x"

{-@ pf :: _ -> { xVar = yVar } @-}
pf () = ()

