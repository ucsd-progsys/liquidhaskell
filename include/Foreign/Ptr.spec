module spec Foreign.Ptr where

measure plen  :: GHC.Ptr.Ptr a -> GHC.Types.Int
measure deref :: GHC.Ptr.Ptr a -> a

type PtrN a N = {v: (PtrV a)        | (plen v)  = N }
type PtrV a   = {v: (GHC.Ptr.Ptr a) | 0 <= (plen v) }

GHC.Ptr.castPtr :: p:(PtrV a) -> (PtrN b (plen p))

GHC.Ptr.plusPtr :: base:(GHC.Ptr.Ptr a)
                -> off:{v:Int | v <= (plen base) } 
                -> {v:(GHC.Ptr.Ptr b) | (plen v) = (plen base) - off }

GHC.Ptr.minusPtr :: p:(GHC.Ptr.Ptr a)
                 -> q:(GHC.Ptr.Ptr b)
                 -> {v:Int | v = (plen p) - (plen q) }
