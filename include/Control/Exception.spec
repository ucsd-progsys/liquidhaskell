module spec Control.Exception where

-- Useless as compiled into GHC primitive, which is ignored
assume assert                       :: {v:Bool | (? (Prop v))} -> a -> a

-- Hack into wiredIn
-- assume GHC.IO.Exception.assertError :: {v:Bool | (? v)} -> GHC.Prim.Addr# -> a -> a
