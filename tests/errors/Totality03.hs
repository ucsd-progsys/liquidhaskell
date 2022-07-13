
-- | Demonstrate that handling only C is total, because A trivially-holds and B
-- is trivially-impossible. There's no error. (Compare to Totality02 and
-- Totality00)

module Totality03 where

data Cases = A | B | C

opaque :: Cases -> Bool
opaque _ = True
{-@ reflect opaque @-}

{-@
proofGetNumIsNat :: { x:Cases | x /= B } -> { x == A || opaque x } @-}
proofGetNumIsNat :: Cases -> ()
proofGetNumIsNat C = () `const` opaque C -- nontrivial-subgoal-holds
