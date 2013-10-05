module spec GHC.Ptr where

GHC.Ptr.castPtr :: p:(PtrV a) -> (PtrN b (plen p))

GHC.Ptr.plusPtr :: base:(PtrV a)
                -> off:{v:GHC.Types.Int | v <= (plen base) }
                -> {v:(PtrV b) | (((pbase v) = (pbase base)) && ((plen v) = (plen base) - off))}

GHC.Ptr.minusPtr :: q:(PtrV a)
                 -> p:{v:(PtrV b) | (((pbase v) = (pbase q)) && ((plen v) >= (plen q)))}
                 -> {v:Nat | v = (plen p) - (plen q)}

measure deref     :: GHC.Ptr.Ptr a -> a

