{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
module CString where 
import LString 

bar :: [a] -> () 
{-@ bar :: xs:{[a] | 0 < len xs} -> {myhead xs == True } @-} 
bar xs@(_:_) = ()