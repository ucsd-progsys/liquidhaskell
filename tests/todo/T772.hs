{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

module LiquidR where

class R m where

class (R a, R b) => UnarySubscript a b where
  indexUnary :: a -> b -> [a]

{-@ instance (R t, R u) => UnarySubscript t u where
      indexUnary :: a:t -> b:{v:_ | 1 + 2 = 3 } -> t
  @-}
instance (R a, R b) => UnarySubscript a b

-- Note this works:
--   indexUnary :: a:t -> b:{v:_ | 1 + 2 = 3 } -> [t]

{-@ predicate Bloop A = (size A) = 0 @-}

-- UNCOMMENT; (error omitted for brevity)
{-@ class (R t, R u, R v) => Addition t u v where
    add :: a:t ->
           b:u ->
          {c:v | ArithmeticResult a b c }
@-}
class (R a, R b, R c) => Addition a b c | a b -> c  where
  add  :: a -> b -> c
  add  = unimplemented
