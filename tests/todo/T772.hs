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
