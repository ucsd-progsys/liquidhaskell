
module List01 where

data L a = N | C a (L a)

mapL f N = N
mapL f (C x xs) = C (f x) (mapL f xs)

revL                = go N 
  where 
    go acc N        = acc
    go acc (C x xs) = go (C x acc) xs

mapLFlipped N f = N
mapLFlipped (C x xs) f = C (f x) (mapLFlipped xs f)

revLFlipped x = go x N
  where
    go N acc = acc
    go (C x xs) acc = go xs (C x acc)
