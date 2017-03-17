module spec GHC.Prim where

embed GHC.Prim.Int#  as int
embed GHC.Prim.Word# as int
embed GHC.Prim.Addr# as Str

embed GHC.Prim.Double#  as real

measure addrLen :: GHC.Prim.Addr# -> GHC.Types.Int

assume GHC.Types.I# :: x:GHC.Prim.Int# -> {v: GHC.Types.Int | v = (x :: int) }
assume GHC.Prim.+#  :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v: GHC.Prim.Int# | v = x + y}
assume GHC.Prim.-#  :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# -> {v: GHC.Prim.Int# | v = x - y}
assume GHC.Prim.==# :: x:GHC.Prim.Int# -> y:GHC.Prim.Int#
                    -> {v:GHC.Prim.Int# | ((v = 1) <=> x = y)}
assume GHC.Prim.>=# :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# 
                    -> {v:GHC.Prim.Int# | ((v = 1) <=> x >= y)}
assume GHC.Prim.<=# :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# 
                    -> {v:GHC.Prim.Int# | ((v = 1) <=> x <= y)}
assume GHC.Prim.<#  :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# 
                    -> {v:GHC.Prim.Int# | ((v = 1) <=> x < y)}
assume GHC.Prim.>#  :: x:GHC.Prim.Int# -> y:GHC.Prim.Int# 
                    -> {v:GHC.Prim.Int# | ((v = 1) <=> x > y)}

