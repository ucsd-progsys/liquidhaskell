module spec GHC.Types where

assume True  :: {v : Bool | (Prop(v))}
assume False :: {v : Bool | (~ (Prop(v)))}

embed GHC.Types.Double as int






