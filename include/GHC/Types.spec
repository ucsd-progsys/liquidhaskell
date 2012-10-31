module spec GHC.Types where

assume True  :: {v : Bool | (? v)}
assume False :: {v : Bool | (~ (? v))}

-- Reusing GHC names, but maybe thats not the best idea.

measure EQ : Ordering
measure LT : Ordering
measure GT : Ordering
            
measure cmp :: Ordering -> Ordering
cmp (EQ) = { v | v = EQ }
cmp (LT) = { v | v = LT }
cmp (GT) = { v | v = GT }





