module ListLen () where

{-@ autosize OList @-}

data OList a =
     Mt
   | Ln{h :: a, t :: OList a}

{-@ data OList a =
      Mt
    | Ln{h :: a, t :: OList {v:a | h <= v}} @-}

insert :: (Ord a) => a -> OList a -> OList a
insert y Mt        = Ln y Mt
insert y (Ln x xs)
  | y <= x         = Ln y (Ln x xs)
  | otherwise      = Ln x (insert y xs)

