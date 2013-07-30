module spec GHC.Types where

-- TODO: Drop prefix below
assume GHC.Types.EQ :: {v: GHC.Types.Ordering | v = (cmp v) }
assume GHC.Types.LT :: {v: GHC.Types.Ordering | v = (cmp v) }
assume GHC.Types.GT :: {v: GHC.Types.Ordering | v = (cmp v) }

measure cmp :: Ordering -> Ordering
cmp (GHC.Types.EQ) = { v | v = EQ }
cmp (GHC.Types.LT) = { v | v = LT }
cmp (GHC.Types.GT) = { v | v = GT }


assume True  :: {v : GHC.Types.Bool | (Prop(v))}
assume False :: {v : GHC.Types.Bool | (~ (Prop(v)))}

embed GHC.Types.Double as int






