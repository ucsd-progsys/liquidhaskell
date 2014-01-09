module DataBase () where

data Rec s v = R (s -> v)
type DBRec = Rec String Value

get :: String -> DBRec -> Value 
get i (R a) = a i

set :: String -> Value -> DBRec -> DBRec
set i x (R a) = R $ \k -> if k == i then x else a k

{-@ empty :: Rec {v:String|0=1} {v : DataBase.Value | v = DataBase.BOT} @-}
empty :: Rec String Value
empty = R $ const BOT

data Value = BOT
           | INT Int 
           | BOOL Bool 
           | STRING String
--            | VEC Value Int


append a1 a2 = \k -> case a1 k of 
                     BOT -> a2 k
                     v   -> v
