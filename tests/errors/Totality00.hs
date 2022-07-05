
-- | Demonstrate the three kinds of cases in a proof. There's no error.

module Totality00 where

data Cases = A | B | C

opaque :: Cases -> Bool
opaque _ = True
{-@ reflect opaque @-}

{-@
proofGetNumIsNat :: { x:Cases | x /= B } -> { x == A || opaque x } @-}
proofGetNumIsNat :: Cases -> ()
proofGetNumIsNat A = () -- trivial-holds
proofGetNumIsNat B = () -- trivial-impossible
proofGetNumIsNat C = () `const` opaque C -- nontrivial-subgoal-holds

-- {-@
-- proofGetNumIsNat' :: { x:Cases | x /= B } -> { x == A || opaque x } @-}
-- proofGetNumIsNat' :: Cases -> Proof
-- proofGetNumIsNat' A = trivial
-- proofGetNumIsNat' B = impossible ""
-- proofGetNumIsNat' C = opaque C *** QED
