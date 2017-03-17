{-@ checkNat :: Nat -> Int @-} 
checkNat :: Int -> Int 
checkNat x = x

unsound :: Int
unsound = checkNat (-1)


data TestBS = TestBS Int deriving (Read)

-- | Possible fixes
-- | 1. add trust-internals flag to ignore the deriving instances
-- | 2. delete the deriving (Read) instance