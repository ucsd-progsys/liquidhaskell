module spec GHC.Types where

assume True  :: {v : Bool | (? v)}
assume False :: {v : Bool | (~ (? v))}

assume EQ    :: Ordering
assume LT    :: Ordering
assume GT    :: Ordering
