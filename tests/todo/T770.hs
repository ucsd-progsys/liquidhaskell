{- This fails with

```
/Users/rjhala/research/stack/liquidhaskell/.stack-work/install/x86_64-osx/lts-5.9/7.10.3/share/x86_64-osx-ghc-7.10.3/liquidhaskell-0.6.0.0/include/Prelude.spec:43:20: Error: GHC Error

43 | type FF      = {v: Bool          | not (Prop v)}
                        ^

    Not in scope: type constructor or class `Bool'
```

if we UNCOMMENT import (1) then we get the error

```
 /Users/rjhala/research/stack/liquidhaskell/.stack-work/install/x86_64-osx/lts-5.9/7.10.3/share/x86_64-osx-ghc-7.10.3/liquidhaskell-0.6.0.0/include/GHC/CString.spec:7:10: Error: GHC Error

 7 |   -> {v:[Char] | v ~~ x && len v == strLen x}
              ^

     Not in scope: type constructor or class `Char'
```

if we UNCOMMENT import (2) then we get no errors

-}

module Wrenn where

import Prelude ()

import Data.Int

-- (1) import Data.Bool
-- (2) import Data.Char

incr :: Int
incr = 1
