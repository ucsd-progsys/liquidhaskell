module spec GHC.Ptr where

measure pbase     :: Foreign.Ptr.Ptr a -> GHC.Types.Int
measure plen      :: Foreign.Ptr.Ptr a -> GHC.Types.Int
measure isNullPtr :: Foreign.Ptr.Ptr a -> Prop

invariant {v:Foreign.Ptr.Ptr a | 0 <= plen  v }
invariant {v:Foreign.Ptr.Ptr a | 0 <= pbase v }

type PtrN a N = {v: (PtrV a)        | (plen v)  = N }
type PtrV a   = {v: (GHC.Ptr.Ptr a) | 0 <= (plen v) }

GHC.Ptr.castPtr :: p:(PtrV a) -> (PtrN b (plen p))

GHC.Ptr.plusPtr :: base:(PtrV a)
                -> off:{v:GHC.Types.Int | v <= (plen base) }
                -> {v:(PtrV b) | (((pbase v) = (pbase base)) && ((plen v) = (plen base) - off))}

GHC.Ptr.minusPtr :: q:(PtrV a)
                 -> p:{v:(PtrV b) | (((pbase v) = (pbase q)) && ((plen v) >= (plen q)))}
                 -> {v:Nat | v = (plen p) - (plen q)}

measure deref     :: GHC.Ptr.Ptr a -> a

