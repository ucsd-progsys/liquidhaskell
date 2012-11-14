module Ex where


-- Existentials introduce scoping problems

{-@ foo :: forall a <p :: x0:Int -> x1:a -> Bool>. 
             (exists [w:{v:Int | v = 0}]. a <p w>) ->
             (exists [w1:{v:Int | v = 0}]. a <p w1>) @-}
foo :: a -> a
foo x = x
