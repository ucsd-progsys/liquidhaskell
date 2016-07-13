module spec Data.String where

embed GHC.Types.Char as Char
// ----------------------------------------------------------------------------------------------
// -- | Logical Set Operators: Interpreted "natively" by the SMT solver -------------------------
// ----------------------------------------------------------------------------------------------

// len
measure stringLen    :: String -> Int 

// substr
measure subString :: String -> Int -> Int -> String 
