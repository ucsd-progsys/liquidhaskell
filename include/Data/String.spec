module spec Data.String where

embed GHC.Types.Char as Char
// ----------------------------------------------------------------------------------------------
// -- | Logical Set Operators: Interpreted "natively" by the SMT solver -------------------------
// ----------------------------------------------------------------------------------------------

// len
// Move this definition to Prelude.hquals to make sure it is always imported
// measure stringLen    :: String -> Int 

// substr
measure subString :: String -> GHC.Types.Int -> GHC.Types.Int -> String 
