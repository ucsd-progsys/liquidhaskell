module Alias00 where
-- tests that we don't normalize the bodies of aliases 

data Zog = V 

{-@ predicate MMin V X Y = (if X < Y then V = X else V = Y) @-}

thing :: Int 
thing = 12 
{-@ thing :: { MMin 1 1 2 } @-}

main :: IO ()
main = pure ()
