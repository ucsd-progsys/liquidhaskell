module spec Data.String where

embed GHC.Types.Char as Char
// ----------------------------------------------------------------------------------------------
// -- | Logical Set Operators: Interpreted "natively" by the SMT solver -------------------------
// ----------------------------------------------------------------------------------------------

// len
// stringLen was already hard-coded
// measure stringLen    :: String -> Int 

// substr
measure subString :: String -> GHC.Types.Int -> GHC.Types.Int -> String 
