module Test.Target.Expr where

import Language.Fixpoint.Types


eq :: Expr -> Expr -> Expr
eq  = PAtom Eq
infix 4 `eq`

ge :: Expr -> Expr -> Expr
ge  = PAtom Ge
infix 5 `ge`

le :: Expr -> Expr -> Expr
le  = PAtom Le
infix 5 `le`

gt :: Expr -> Expr -> Expr
gt  = PAtom Gt
infix 5 `gt`

lt :: Expr -> Expr -> Expr
lt  = PAtom Lt
infix 5 `lt`

iff :: Expr -> Expr -> Expr
iff = PIff
infix 3 `iff`

imp :: Expr -> Expr -> Expr
imp = PImp
infix 3 `imp`


app :: Symbolic a => a -> [Expr] -> Expr
-- app f es = EApp (dummyLoc $ symbol f) es
app = mkEApp . dummyLoc . symbol

var :: Symbolic a => a -> Expr
var = EVar . symbol

-- prop :: Symbolic a => a -> Expr
-- prop = PBexp . EVar . symbol
prop :: Expr -> Expr
prop = id

instance Num Expr where
  fromInteger = ECon . I . fromInteger
  (+) = EBin Plus
  (-) = EBin Minus
  (*) = EBin Times
  abs = error "abs of Liquid.Fixpoint.Types.Expr"
  signum = error "signum of Liquid.Fixpoint.Types.Expr"

-- instance Real Expr where
--   toRational (ECon (I i)) = fromIntegral i
--   toRational x            = error $ "toRational: " ++ show x

-- instance Enum Expr where
--   toEnum = ECon . I . fromIntegral
--   fromEnum (ECon (I i)) = fromInteger i
--   fromEnum x            = error $ "fromEnum: " ++ show x

-- instance Integral Expr where
--   div = EBin Div
--   mod = EBin Mod
--   quotRem x y = (x `div` y, x `mod` y)
--   toInteger (ECon (I i)) = i
--   toInteger x            = error $ "toInteger: " ++ show x
