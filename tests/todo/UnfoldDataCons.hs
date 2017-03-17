
{-@ boo :: [{v:a | false }] -> {v:[a] | len v == 0 } @-}
boo :: [a] -> [a]
boo []     = [] 
boo (x:xs) = (x:xs)


{-@ foo :: [{v:a | false }] -> {v:[a] | len v == 0 } @-}
foo :: [a] -> [a]
foo x = x 
