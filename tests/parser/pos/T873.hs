module T873 where

{-@ type TypeName = String @-}
type TypeName = String

{-@
data Type <p :: Int -> Bool>
  = TVar (v :: Int <p v>)
  | TCon TypeName [Type <p>]  // TypeName has to be within parens
@-}

data Type
  = TVar Int
  | TCon TypeName [Type]
