module spec GHC.Types where

// TODO: Drop prefix below
// GHC.Types.EQ :: {v:GHC.Types.Ordering | v = (cmp v) }
// GHC.Types.LT :: {v:GHC.Types.Ordering | v = (cmp v) }
// GHC.Types.GT :: {v:GHC.Types.Ordering | v = (cmp v) }

// measure cmp :: GHC.Types.Ordering -> GHC.Types.Ordering
// cmp GHC.Types.EQ = { v | v = GHC.Types.EQ }
// cmp GHC.Types.LT = { v | v = GHC.Types.LT }
// cmp GHC.Types.GT = { v | v = GHC.Types.GT }


GHC.Types.True  :: {v:GHC.Types.Bool | v     }
GHC.Types.False :: {v:GHC.Types.Bool | (~ v) }


GHC.Types.isTrue#  :: n:_ -> {v:GHC.Types.Bool | ((n = 1) <=> ((v)))}


GHC.Types.W# :: w:_ -> {v:GHC.Types.Word | v == w }

embed GHC.Types.Int      as int
embed GHC.Types.Bool     as bool

measure autolen :: forall a. a -> GHC.Types.Int
class measure len :: forall f a. f a -> GHC.Types.Int
instance measure len :: forall a. [a] -> GHC.Types.Int
len []     = 0
len (y:ys) = 1 + len ys
invariant {v: [a] | len v >= 0 }
