module RG where


data RGRef a 

{-@ measure terminalValue :: RGRef a -> a @-}
{-@ qualif TerminalValue(r:RGRef a): (terminalValue r) @-}
