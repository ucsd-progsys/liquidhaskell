module Ex where


-- Existentials introduce scoping problems

{-@ foo :: forall a <p :: x0:Int -> x1:a -> Bool>. 
             a <p 0> -> a <p 42> @-}
foo :: a -> a
foo x = x
