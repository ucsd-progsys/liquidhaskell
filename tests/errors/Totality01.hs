{-@ LIQUID "--expect-error-containing=is not a subtype of the required type" @-}

-- | Demonstrate that case C is indeed a subgoal by removing the evidence.
-- (Compare to Totality00)

module Totality01 where

data Cases = A | B | C

opaque :: Cases -> Bool
opaque _ = True
{-@ reflect opaque @-}

{-@
proofGetNumIsNat :: { x:Cases | x /= B } -> { x == A || opaque x } @-}
proofGetNumIsNat :: Cases -> ()
proofGetNumIsNat A = () -- trivial-holds
proofGetNumIsNat B = () -- trivial-impossible
proofGetNumIsNat C = () -- FAIL
