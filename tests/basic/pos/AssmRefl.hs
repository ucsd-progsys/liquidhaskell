-- | test if basic assume reflect Lis functioning 
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Inc00 where

{-@ assume reflect myeven as even @-}
myeven :: Int -> Bool 
myeven x = False

{-@ test :: { not (even 5) } @-} 
test :: ()
test = ()