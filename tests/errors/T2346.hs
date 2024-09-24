{-@ LIQUID "--expect-error-containing=?b == GHC.Types.[]" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--exactdc" @-}

-- | Tests that error messages show sufficient information.
-- In particular, we want to see the @?b@ binding below, that
-- tells that @?a == []@
--
-- > Test.hs:13:25: error:
-- >     Liquid Type Mismatch
-- >     .
-- >     The inferred type
-- >       VV : {v : () | v == GHC.Tuple.()}
-- >     .
-- >     is not a subtype of the required type
-- >       VV : {VV##718 : () | Test.append ?a GHC.Types.[] == ?a}
-- >     .
-- >     in the context
-- >       ?a : {?a : [a] | len ?a >= 0}
-- >
-- >       ?b : {?b : [a] | ?b == ?a
-- >                        && ?b == GHC.Types.[]
-- >                        && len ?b == 0
-- >                        && len ?b >= 0}
-- >     Constraint id 12
-- >    |
-- > 13 | append_empty_right [] = ()
-- >    |
--
module T2346 where

{-@ reflect append @-}
append :: [a] -> [a] -> [a]
append [] ys = ys
append (x:xs) ys = x : append xs ys

{-@ append_empty_right :: xs:[a] -> { append xs [] == xs } @-}
append_empty_right :: [a] -> ()
append_empty_right [] = ()
append_empty_right (x:xs) =
    case append (x:xs) [] of
      [] -> append_empty_right xs
      _ -> append_empty_right xs
