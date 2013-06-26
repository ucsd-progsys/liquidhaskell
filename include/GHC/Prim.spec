module spec GHC.Prim where

embed GHC.Prim.Int#  as int
embed GHC.Prim.Addr# as int


measure addrLen :: GHC.Prim.Addr# -> Int



assume GHC.Types.I# :: x:GHC.Prim.Int# -> {v: GHC.Types.Int | v = (x :: Int) }   
assume GHC.Prim.+#  :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v: GHC.Prim.Int# | v = x + y}
assume GHC.Prim.-#  :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v: GHC.Prim.Int# | v = x - y}
assume GHC.Prim.==# :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v:Bool | (Prop(v) <=> x =  y)}
assume GHC.Prim.>=# :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v:Bool | (Prop(v) <=> x >= y)}
assume GHC.Prim.<=# :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v:Bool | (Prop(v) <=> x <= y)}
assume GHC.Prim.<#  :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v:Bool | (Prop(v) <=> x <  y)}
assume GHC.Prim.>#  :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v:Bool | (Prop(v) <=> x >  y)}

