{-# LANGUAGE TemplateHaskell #-}

{-@ LIQUID "--no-termination" @-}

import Axiomatize

data L a = N | C a (L a)


{-@ axiomatize append @-}
$(axiomatize
  [d| append :: L a -> L a -> L a
      append xs N = xs
      append xs (C y ys) = xs
    |])

$(axiomatize
      [d| appendCase xs ys = case xs of {N -> ys; C x xs -> C x (append xs ys)}
    |])

use_axiomN, use_axiomCaseN :: L a -> Proof
use_axiomN xs = axiom_append_N xs
use_axiomCaseN = axiom_appendCase_xs_is_N

use_axiomC, use_axiomCaseC :: L a -> a -> L a -> Proof
use_axiomC = axiom_append_C
use_axiomCaseC = axiom_appendCase_xs_is_C
