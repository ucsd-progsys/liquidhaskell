


data IncList a = Emp | a :< IncList a 

merge :: (Ord a) => IncList a -> IncList a -> IncList a
merge Emp Emp = Emp
merge Emp ys = ys
merge (x :< xs) (y :< ys)
  | x <= y    = x :< merge xs (y :< ys)
  | otherwise = y :< merge (x :< xs) ys