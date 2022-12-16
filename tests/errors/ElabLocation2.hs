{-@ LIQUID "--expect-error-containing=ElabLocation2.hs:18:54-66" @-}
module ElabLocation2 where
type Range = (Int,Int)

{-@ measure start @-}
start :: Range -> Int
start (a,b) = a

{-@ measure end @-}
end :: Range -> Int
end (a,b) = b

{-@ using (Range) as {r:Range | start r <= end r} @-}

-- seemed to work earlier, now fails
{-@ intsToRanges :: Int -> Int -> Int -> Int -> Maybe (Range,Range) @-}
intsToRanges :: Int -> Int -> Int -> Int -> Maybe (Range,Range)
intsToRanges a b c d = if a <= b && c <= d then Just ((a,b),(c,d)) else Nothing
