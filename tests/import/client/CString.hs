{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
module CString where 
import LString 

bar :: [a] -> () 
{-@ bar :: xs:{[a] | true } -> {myhead xs} @-} 
bar xs = ()