{-@ LIQUID "--expect-error-containing=Illegal type specification for `UnboundVarInSpec.foo`" @-}
module UnboundVarInSpec where


{-@ foo :: forall <p :: s -> s -> Bool>.
                   xs:s<p y> -> s<p xs> @-}
foo :: s -> s
foo s = s
