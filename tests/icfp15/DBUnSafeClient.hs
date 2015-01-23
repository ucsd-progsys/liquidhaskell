module DBUnSafeClient where

import DataBase

import Prelude hiding (product)

data Value = VA | VB | VC | VD

data Tag = TA | TB | TC | TD   
         deriving Eq


rab :: Dict Tag Value
{-@ rab :: {v:Dict <{\v -> v = TA || v = TB }, {\i v -> (i == TA => v = VA) && (i == TB => v = VB)} > Tag Value | (listElts (dom v) = Set_cup (Set_sng TA) (Set_sng TB) ) } @-}
rab = extend TB VB $ extend TA VA empty

rcd :: Dict Tag Value
{-@ rcd :: Dict <{\v -> v = TC || v = TD }, {\i v -> (i == TC => v = VC) && (i == TD => v = VD)} > Tag Value @-}
rcd = extend TC VC $ extend TD VD empty


rabcd :: Dict Tag Value
{-@ rabcd :: Dict <{\v -> v = TA || v = TB || v = TC || v = TD }, {\i v -> (i == TC => v = VC) && (i == TD => v = VD)} > Tag Value @-}
rabcd = product rab rcd


rfail1 :: Dict Tag Value
rfail1 = product rab rabcd

rfail2 :: Dict Tag Value
rfail2 = project [TC] rab

