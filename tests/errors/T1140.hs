
module Blank where 
	
data Label = Label Int 

type Proof = () 

{-@ foo :: Label -> Label -> Label -> Proof @-} 
foo :: Label -> Label -> Label -> Proof -> Proof 
foo a b c v = ()

