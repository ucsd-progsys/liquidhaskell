# TODO

## PLE-OPT

Use tries to make PLE "incremental"

```haskell
data Trie a
  = Node ![Branch a]
  deriving (Eq, Show)

data Branch a
  = Bind !Key !(Trie a)
  | Val a
  deriving (Eq, Show)

type Result  = M.HashMap Key !Expr

type CTrie   = Trie SubcId

type Context = [Expr]                      -- ultimately, the SMT context 

trieInstantiate :: Env -> CTrie -> Result


loop :: Env -> [Expr] -> 
```