module HOSubtype where

{-@ foo :: f:(x:{v:Int | false} -> {v:Int | v = x}) -> () @-}
foo    :: (Int -> Int) -> ()
foo pf = ()

test0 :: ()
test0  = foo useless_proof

{-@ generic_accept_stable ::
                    f:(x:a -> {v:a | (v = x)}) ->
                    ()
                    @-}
generic_accept_stable :: (a -> a) -> ()
generic_accept_stable pf = ()

{-@ useless_proof :: x:{v:Int | v > 0} -> {v:Int | v > 0} @-}
useless_proof :: Int -> Int
useless_proof _ = 5

test :: ()
test = generic_accept_stable useless_proof
