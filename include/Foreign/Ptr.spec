module spec Foreign.Ptr where

measure plen  :: Foreign.Ptr a -> GHC.Types.Int

type PtrN a N = {v: (PtrV a)        | (plen v)  = N }
type PtrV a   = {v: (Ptr a)         | 0 <= (plen v) } 

GHC.Ptr.castPtr :: p:(PtrV a) -> (PtrN b (plen p))
GHC.Ptr.plusPtr :: base:(Ptr a) -> off:{v:Int | v <= (plen base) } -> {v:(Ptr b) | (plen v) = (plen base) - off }
