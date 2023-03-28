{-@ LIQUID "--reflection" @-}
module B  where 
import Language

{-@ reflect subst @-}
subst :: Expr l st r -> Expr l st r 
subst EUnit  = EUnit
subst e  = e 