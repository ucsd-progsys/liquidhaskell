module spec GHC.Types where

// TODO: Drop prefix below
GHC.Types.EQ :: {v:GHC.Types.Ordering | v = (cmp v) }
GHC.Types.LT :: {v:GHC.Types.Ordering | v = (cmp v) }
GHC.Types.GT :: {v:GHC.Types.Ordering | v = (cmp v) }

measure cmp :: GHC.Types.Ordering -> GHC.Types.Ordering
cmp GHC.Types.EQ = { v | v = GHC.Types.EQ }
cmp GHC.Types.LT = { v | v = GHC.Types.LT }
cmp GHC.Types.GT = { v | v = GHC.Types.GT }


GHC.Types.True  :: {v:GHC.Types.Bool | (Prop(v))}
GHC.Types.False :: {v:GHC.Types.Bool | (~ (Prop(v)))}


GHC.Types.isTrue#  :: n:_ -> {v:GHC.Types.Bool | ((n = 1) <=> (Prop(v)))}





