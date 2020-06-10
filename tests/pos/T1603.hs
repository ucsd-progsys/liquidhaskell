{-@ LIQUID "--reflect" @-}

module T1603 where

{-@ reflect rAnd @-}
rAnd :: Bool
rAnd = and [True,False,True]

{-@ reflect rOr @-}
rOr :: Bool
rOr = or [True,False,True]

