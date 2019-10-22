{-@ LIQUID "--typed-holes" @-}

-- This is to test `nilDataCons`.
{-@ oneElem :: xs:a -> {v:[a] | len v == 1} @-}
oneElem :: a -> [a]
oneElem x = _oneElem
