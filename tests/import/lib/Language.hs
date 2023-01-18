module Language where

data Expr l st r = EUnit | EFalse Int 
{-@ data Expr l st r = EUnit | EFalse { elb1 :: {xxx:Int | false}}  @-}


{-@ measure isEFalse @-}
isEFalse :: Expr l st r -> Bool 
isEFalse (EFalse _ ) = True 
isEFalse _ = False 