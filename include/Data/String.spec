module spec Data.String where

embed GHC.Types.Char as Char
// ----------------------------------------------------------------------------------------------
// -- | Logical Set Operators: Interpreted "natively" by the SMT solver -------------------------
// ----------------------------------------------------------------------------------------------

// len
measure str.len    :: String -> Int 

// substr
measure str.substr :: String -> Int -> Int -> String 
