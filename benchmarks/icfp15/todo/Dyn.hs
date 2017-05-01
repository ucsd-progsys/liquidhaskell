module Dyn where

data Dyn = Int Int | String String | Bool Bool 
type Key = String
data Box = Record Key Dyn

emp :: Box
emp = undefined

class Value v where
  toDyn   :: v -> Dyn
  fromDyn :: Dyn -> v
 
put :: (Value v) => Key -> v -> Box -> Box
put k v b = insert k b (toDyn v) 

get :: (Value v) => Box -> Key -> v
get = undefined

rj  :: Box
rj  = put "name"     "Ranjit" 
    $ put "age"      10
    $ put "sleeping" True
    $ emp 

out = "My name is " ++ get rj "name"


sumXY box x y = get box x + get box y


















 
