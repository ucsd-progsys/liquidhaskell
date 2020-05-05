module spec Liquid.Prelude.Totality where

assume Control.Exception.Base.patError :: {v:GHC.Prim.Addr# | 5 <4 } -> a
assume Control.Exception.Base.recSelError :: {v:GHC.Prim.Addr# | 5 < 4 } -> a
assume Control.Exception.Base.nonExhaustiveGuardsError :: {v:GHC.Prim.Addr# | 5 < 4 } -> a
assume Control.Exception.Base.noMethodBindingError :: {v:GHC.Prim.Addr# | 5 < 4 } -> a

//This one doesn't exist anymore in modern base.
//Control.Exception.Base.irrefutPatError :: {v:GHC.Prim.Addr# | 5 < 4 } -> a
