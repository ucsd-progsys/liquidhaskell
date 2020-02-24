module spec GHC.Prim where 

embed GHC.Prim.Int#     as int
embed GHC.Prim.Addr#    as Str
embed GHC.Prim.Char#    as Char
embed GHC.Prim.Double# as real
embed GHC.Prim.Float#  as real
embed GHC.Prim.Word#    as int
