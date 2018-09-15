{-@ LIQUID "--structural" @-}

data L a = N | C a (L a)

mapL f N = N
mapL f (C x xs) = C (f x) (mapL f xs)

revL                = go N 
  where 
    go acc N        = acc
    go acc (C x xs) = go (C x acc) xs

