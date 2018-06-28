{-@ assume errorWithoutStackTrace :: {i:String | false } -> a @-} 

{-@ minimumBy               :: (a -> a -> Ordering) -> {i:[a] | ?? } -> a @-}
minimumBy               :: (a -> a -> Ordering) -> [a] -> a
minimumBy _ []          =  errorWithoutStackTrace "List.minimumBy: empty list"
minimumBy cmp xs        =  foldl1 minBy xs
                        where
                           minBy x y = case cmp x y of
                                       GT -> y
                                       _  -> x

