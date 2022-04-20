-- TEST: the "transitively" imported name `FunClashLibLib.incr` is fully qualified and so 
-- SHOULD NOT get resolved to `FunClashLibLibClient.incr`; we allow this for "re-exported" names,
-- e.g. to let `Data.Vector.Vector` get resolved to `Data.Vector.Generic.Vector` ... 
-- but SOMEHOW block this. [Current workaround: make sure you import-qualified `FunClashLibLib` 
-- so that the name "attaches" properly. sigh.

module FunClashLibLibClient where

import FunClashLib

incr :: Bool -> Bool
incr = not 
