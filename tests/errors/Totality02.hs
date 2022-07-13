{-@ LIQUID "--expect-error-containing=Totality error: missing `Totality02.C` case" @-}

-- | Demonstrate that handling only A is nontotal, because C is a subgoal that
-- LH cannot prove by itself. (Compare to Totality00)

module Totality02 where

data Cases = A | B | C

opaque :: Cases -> Bool
opaque _ = True
{-@ reflect opaque @-}

{-@
proofGetNumIsNat :: { x:Cases | x /= B } -> { x == A || opaque x } @-}
proofGetNumIsNat :: Cases -> ()
proofGetNumIsNat A = () -- trivial-holds
