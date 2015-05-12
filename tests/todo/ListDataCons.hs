module Fixme where


{-@ hsig :: x:a -> {v:[a] | v == (x:[])} @-} 
hsig :: a -> [a] 
hsig x = [x] 


{-

This crashes with 

(VV#F1 = fix#GHC.Types.#58##35#64([x#aJP; fix#GHC.Types.#91##93##35#6m([])]))

z3Pred: error converting (VV#F1 = fix#GHC.Types.#58##35#64([x#aJP; fix#GHC.Types.#91##93##35#6m([])]))
Fatal error: exception Failure("bracket hits exn: TpGen.MakeProver(SMT).Z3RelTypeError
")

Unless these edits

https://github.com/ucsd-progsys/liquid-fixpoint/commit/63e1e1ccfbde4d7a26bd3e328ad111423172a7e9


-}
