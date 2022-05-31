{-@ LIQUID "--expect-any-error" @-}
{-@ LIQUID "--reflection" @-}

module T1553 where

negPos :: (a -> ()) -> ()
{-@ assume negPos :: (a -> {v:() | 0 == 1 }) -> {v:() | 0 == 1 } @-}
negPos _ = () 
    
testBad :: a -> () 
{-@ testBad :: a -> {v:() | 0 == 1 } @-}
testBad _ = negPos (\_ -> ()) 
    
{-@ getUnsound :: () -> {v:() | 0 == 1 } @-}
getUnsound :: () -> () 
getUnsound _ = testBad () 
    
posPos :: a -> () -> ()
{-@ posPos :: a -> {v:() | 0 == 1 } -> {v:() | 0 == 1 } @-}
posPos _ _ = () 
    
testOK :: a -> () 
{-@ testOK :: a -> {v:() | 0 == 1 } @-}
testOK x = posPos x () 
