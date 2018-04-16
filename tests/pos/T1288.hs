
{-@ measure foo @-}
foo :: () -> Int
foo _ = 0

{-@ measure bar @-}
bar :: () -> Int
bar () = 0
