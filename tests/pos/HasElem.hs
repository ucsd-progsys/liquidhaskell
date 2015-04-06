module HasElem where


data L a = Zero | One a

{-@ measure hasElem @-}
hasElem :: Eq a => a -> L a -> Bool
hasElem _ Zero    = False
hasElem x (One y) = x == y
