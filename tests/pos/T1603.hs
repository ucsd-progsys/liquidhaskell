{-@ LIQUID "--reflect" @-}

{-@ reflect rAnd @-}
rAnd :: Bool
rAnd = and [True,False,True]

{-@ reflect rOr @-}
rOr :: Bool
rOr = or [True,False,True]

