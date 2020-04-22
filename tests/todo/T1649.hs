{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE GADTs           #-}
{-# LANGUAGE KindSignatures  #-}
{-@ LIQUID "--reflection" @-} 
-- Z3 encoding cannot be used until this is fixed: 
-- https://github.com/Z3Prover/z3/issues/3930
{- LIQUID "--no-adt"         @-} 
{-@ LIQUID "--ple-local"      @-} 

module Properties where 


{-@ assume injectiveEqRTFun :: x:(a->b) -> y:(a->b) -> d:{EqRT (a->b) {x} {y} | isEqFun d} 
                         -> {x = eqFunX d && y = eqFunY d} @-}
injectiveEqRTFun :: (a->b) -> (a->b) -> EqT (a->b) -> () 
injectiveEqRTFun _ _ _ = () 

{-@ measure isEqFun @-}
isEqFun :: EqT a -> Bool 
isEqFun (EqFun _ _ _) = True 
isEqFun _             = False 

{-@ reflect eqFunX @-}
{-@ eqFunX :: {d:EqT (a -> b) | isEqFun d} -> (a -> b) @-}
eqFunX :: EqT (a -> b) ->  (a -> b) 
eqFunX (EqFun x _ _) = x 

{-@ reflect eqFunY @-}
{-@ eqFunY :: {d:EqT (a -> b) | isEqFun d} -> (a -> b) @-}
eqFunY :: EqT (a -> b) ->  (a -> b) 
eqFunY (EqFun _ y _) = y 


{-@ ple     eqFunP @-}
{- reflect eqFunP @-}
-- STATUS: assertion passes, but result type still fails 
{-@ eqFunP :: d:{EqT (a -> b) | isEqFun d} -> x:a -> EqRT b {eqFunX d x} {eqFunY d x} @-}
eqFunP :: EqT (a -> b) ->  a -> EqT b
eqFunP (EqFun f g p) = p
eqFunP _ = error "impossible"


assert :: Bool -> a -> a 
{-@ assert :: {b:Bool | b} -> x:a -> {v:a | v == x && b} @-}
assert _ x = x 

{-@ assume eqT :: x:a -> y:a -> {v:Bool | v <=> eqT x y} @-}
eqT :: a -> a -> Bool 
eqT = undefined 


{-@ measure eqT :: a -> a -> Bool @-}
{-@ type EqRT a E1 E2 = {v:EqT a | eqT E1 E2} @-}


data EqT  :: * -> *  where 
   EqSMT  :: Eq a => a -> a -> (a -> [a]) -> EqT a 
   EqFun  :: (a -> b) -> (a -> b) -> (a -> EqT b) -> EqT (a -> b)

{-@ data EqT  :: * -> *  where 
     EqSMT  :: Eq a => x:a -> y:a -> (a -> {v:[a] | 0 < len v}) -> EqRT a {x} {y}
   | EqFun  :: ff:(a -> b) -> gg:(a -> b) -> (x:a -> {d:EqT b | eqT (ff x) (gg x)}) -> EqRT (a -> b) {ff} {gg}
@-}   