{-@ LIQUID "--reflection" @-}

module C where 
import Language
import B

{-@ getVal :: {e:Expr l st r | isEFalse e } -> {v:Int | false} @-}
getVal :: Expr l st r -> Int
getVal (EFalse v) = v 