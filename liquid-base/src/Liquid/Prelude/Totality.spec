module spec Liquid.Prelude.Totality where


measure totalityError :: a -> Bool


assume Control.Exception.Base.patError :: {v:GHC.Prim.Addr# | totalityError "Pattern match(es) are non-exhaustive"} -> a

assume Control.Exception.Base.recSelError :: {v:GHC.Prim.Addr# | totalityError "Pattern match(es) are non-exhaustive"} -> a

assume Control.Exception.Base.nonExhaustiveGuardsError :: {v:GHC.Prim.Addr# | totalityError "Pattern match(es) are non-exhaustive"} -> a

assume Control.Exception.Base.noMethodBindingError :: {v:GHC.Prim.Addr# | totalityError "Pattern match(es) are non-exhaustive"} -> a
