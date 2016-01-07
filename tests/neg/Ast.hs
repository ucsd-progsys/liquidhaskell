-- FAILING TEST: this test SHOULD FAIL BUT DOESN'T
-- issue #519

{-# LANGUAGE DeriveFunctor #-}
module Main where

data AstIndex = IxExpr | IxType

{-@ measure isExprIndex @-}
isExprIndex :: AstIndex -> Bool
isExprIndex IxExpr = True
isExprIndex _      = False

{-@ measure isTypeIndex @-}
isTypeIndex :: AstIndex -> Bool
isTypeIndex IxType = True
isTypeIndex _      = False

data AstF f = Lit Int    AstIndex
            | Var String AstIndex
            | App f f
            | Paren f

{-@
  data AstF f <ix :: AstIndex -> Prop>
    = Lit Int    (i :: AstIndex<ix>)
    | Var String (i :: AstIndex<ix>)
    | App (fn :: f) (arg :: f)
    | Paren (ast :: f)
  @-}

{-@ type AstFE = AstF <{\ix -> isExprIndex ix}> @-}
{-@ type AstFT = AstF <{\ix -> isTypeIndex ix}> @-}


-- Now lets tie the knot!

newtype Fix f = In { out :: f (Fix f) }

type Ast = Fix AstF

{-@ type AstE = Fix AstFE @-}
{-@ type AstT = Fix AstFT @-}

{-@ astExpr :: Fix (AstF <{\ix -> isExprIndex ix}>)  @-}
astExpr :: Ast
astExpr = undefined 

{-@ id1 :: forall <p :: AstIndex -> Prop>. Fix (AstF <p>) -> Fix (AstF <p>)  @-}
id1 :: Fix AstF -> Fix AstF
id1 z = z

{-@ wrong :: AstT @-}
wrong = id1 astExpr