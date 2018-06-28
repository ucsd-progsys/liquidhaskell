module GenericIndex where 

{-@ genericIndex :: (Integral i) => xs:{[a] | ?? } -> i:{i | ?? } -> a @-}
genericIndex :: (Integral i) => [a] -> i -> a
genericIndex (x:_)  0 = x
genericIndex (_:xs) n
 | n > 0     = genericIndex xs (n-1)
 | otherwise = errorWithoutStackTrace "List.genericIndex: negative argument."
genericIndex _ _      = errorWithoutStackTrace "List.genericIndex: index too large."
