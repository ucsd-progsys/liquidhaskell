module spec Foreign.Ptr where 

measure plen  :: Foreign.Ptr a -> GHC.Types.Int

type PtrN a N = {v: (PtrV a)        | (plen v)  = N }
type PtrV a   = {v: (Ptr a)         | 0 <= (plen v) } 

-- invariant {v: Ptr a        | (plen v)  >= 0}


