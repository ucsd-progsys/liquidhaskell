module spec Prelude where

assume Control.Exception.Base.patError :: {v:GHC.Prim.Addr# | false } -> a
assume Control.Exception.Base.irrefutPatError :: {v:GHC.Prim.Addr# | false} -> a
assume Control.Exception.Base.recSelError :: {v:GHC.Prim.Addr# | false} -> a
assume Control.Exception.Base.nonExhaustiveGuardsError :: {v:GHC.Prim.Addr# | false} -> a
assume Control.Exception.Base.noMethodBindingError :: {v:GHC.Prim.Addr# | false} -> a
