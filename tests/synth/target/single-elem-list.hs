{-@ LIQUID "--typed-holes" @-}

{-@ err :: { v: Int | false } -> a @-}
err :: Int -> a
err s = undefined

-- This is to test `nilDataCons`.
{-@ oneElem :: xs:a -> {v:[a] | len v == 1} @-}
oneElem :: a -> [a]
oneElem = _oneElem
