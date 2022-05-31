{-@ LIQUID "--expect-any-error" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module T1814 where

import qualified Data.Set as S 

type Acc = Int 
type Reg = Int 
type Config = (Acc, Mem Reg) 

data Code 
  = Add   Reg Code 
  | Halt 

{-@ exec :: c:Code -> (a::Acc, {m:Mem Int | validMem m c a}) -> Config @-}
exec :: Code -> Config -> Config
exec (Add r c)   (a,m) = exec c (a + get r m ,m) 
exec Halt        (a,m) = (a,m) 


{-@ reflect validMem @-}
validMem :: Mem Int -> Code -> Acc -> Bool 
validMem m (Add r c) a = if S.member r (memAddrs m) then validMem m c (a + get r m) else False
validMem m _ a = True 


{-@ type ValidCode = {c:Code | validMem MEmp c 0 } @-}
{-@ code :: ValidCode  @-} 
code :: Code 
code =  Add 42 Halt


{-@ reflect get   @-}



data Mem v = MEmp | MCons Int v (Mem v)

{-@ measure memAddrs @-}
memAddrs :: Mem v -> S.Set Int
memAddrs MEmp                 = S.empty
memAddrs (MCons addr val mem) = S.union (S.singleton addr) (memAddrs mem)

{-@ get :: addr : Int -> { mem : Mem v | S.member addr (memAddrs mem) } -> v @-}
get :: Int -> Mem v -> v
get addr (MCons addr' val' mem)
  | addr == addr' = val'
  | otherwise     = get addr mem



