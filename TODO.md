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
type CTrie   = Trie   SubcId
type CBranch = Branch SubcId

type Context = [Expr]                      -- ultimately, the SMT context 

trieInstantiate :: Env -> CTrie -> Result


ple1 :: Env -> Context -> Diff -> BindId -> Maybe SubCid -> Expr 
ple1 = undefined

updRes :: Result -> BindId -> Expr -> Result
updRes = undefined

updCtx :: Context -> Expr -> Context
updCtx = undefined


loopT :: Env -> Context -> Diff -> BindId -> Result -> CTrie   -> Result
loopT env ctx delta i res (Node [])  = res
loopT env ctx delta i res (Node [b]) = loopB env ctx delta i res b
loopT env ctx delta i res (Node bs)  = L.foldl' (loopB ctx' delta i) res' bs
  where
    e'                               = ple1 env ctx delta i None
    ctx'                             = updCtx ctx e'
    res'                             = updRes res i e'

loopB :: Env -> Context -> Diff -> BindId -> Result -> CBranch -> Result
loopB env ctx delta i res (Arc i t)  = loopT env ctx (i:delta) i res t
loopB env ctx delta i res (Val cid)  = updRes res i e'
  where
    e'                               = ple1 env ctx delta i (Just cid)

```