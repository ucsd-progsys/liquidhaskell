{-@ LIQUID "--expect-error-containing=Unknown logic name `y`" @-}
module UnboundVarInSpec where


{-@ foo :: forall <p :: s -> s -> Bool>.
                   xs:s<p y> -> s<p xs> @-}
foo :: s -> s
foo s = s
