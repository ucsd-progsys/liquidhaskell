-- | Duplicate assume reflects
{-@ LIQUID "--expect-error-containing=Duplicate reflection of \"alwaysFalse\"" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module AssmRefl04 where

alwaysFalse :: Bool 
alwaysFalse = False

{-@ reflect alwaysTrue @-}
{-@ assume reflect alwaysFalse as alwaysTrue @-}
alwaysTrue :: Bool
alwaysTrue = True

{-@ reflect alwaysFalse2 @-}
{-@ assume reflect alwaysFalse as alwaysFalse2 @-}
alwaysFalse2 :: Bool
alwaysFalse2 = False

{-@ test :: { alwaysFalse } @-} 
test :: ()
test = ()
