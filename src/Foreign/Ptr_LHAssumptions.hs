module Foreign.Ptr_LHAssumptions where


{-@

invariant {v:Foreign.Ptr.Ptr a | 0 <= plen  v }
invariant {v:Foreign.Ptr.Ptr a | 0 <= pbase v }

@-}
