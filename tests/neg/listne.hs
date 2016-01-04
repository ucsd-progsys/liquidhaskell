
{-@ type ListNE a = {v:[a] | 0 < len v} @-}

{-@ junkProp :: ListNE Int @-}
junkProp :: [Int]
junkProp = []

