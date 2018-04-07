{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.Fixpoint.Graph.Congruence where

import Data.Function (on)
import Data.Hashable
import Data.Interned

import qualified Language.Fixpoint.Types as F 

-- 1.  x = y => f x = f y
-- 2.  f(f(f(x))) = x => f(f(f(f(f(x))))) = x => f(x) = a 

examples = [t1, t2]
  where 
    t1   = app "f" [var "x", var "y"] 
    t2   = app "f" [var "x", var "y"] 

{-

data UFSt = U 
  { ufPar   :: M.HashMap Id Term          -- ^ i :-> t      IF term 'i' has union-find parent 't'
  , ufPreds :: M.HashMap Id [(Int, Term)] -- ^ i :-> (j, t) IF term 'i' is 'j'-th arg in application 't'
  }

parent :: Term -> UF (Maybe Term)
parent u = M.lookup (identity u) <$> gets ufPar

find :: Term -> UF Id 
find u = do 
  mbU' <- parent u 
  case mbU' of
    Nothing -> return u 
    Just u' -> find u'  

union :: Term -> Term -> UF () 
union u v = TODO 

preds :: Id -> UF [Term]
preds = TODO 


isCong :: Term -> Term -> UF Bool 
isCong = TODO 

isEq :: Term -> Term -> UF Bool 
isEq u v = do 
  ui <- find u 
  vi <- find v 
  return (ui == vi)

congMerge :: (Int, Term) -> (Int, Term) -> UF ()
congMerge (i, u) (j, v) 
  | i == j = ifM (isEq u v) 
              (return ())
              (ifM (isCong u v) 
                (merge u v)
                (return ())
  | otherwise = return ()  

merge :: Term -> Term -> UF ()
merge u v = do 
  ui <- find u
  vi <- find v 
  if ui == vi 
    then return ()
    else do 
      uPs <- preds ui 
      vPs <- preds vi 
      union u v
      forM_ uPs $ \u' ->
        forM_ vPs $ \v' -> 
          congMerge u' v'
 -}    


--------------------------------------------------------------------------------
-- | Exported Constructors
--------------------------------------------------------------------------------
app :: F.Symbol -> [Term] -> Term
app f as = intern (BApp f as)

var :: F.Symbol -> Term
var x = intern (BVar x)

--------------------------------------------------------------------------------
-- | Hash-consed Term DataType
--------------------------------------------------------------------------------
data Term 
  = Var   {-# UNPACK #-} !Id !F.Symbol 
  | App   {-# UNPACK #-} !Id !F.Symbol [Term]
--------------------------------------------------------------------------------

data UninternedTerm
  = BVar !F.Symbol 
  | BApp !F.Symbol [Term] 

instance Interned Term where
  type Uninterned Term  = UninternedTerm
  data Description Term = DVar F.Symbol
                        | DApp F.Symbol [Id]
                          deriving Show
  describe (BApp f as)  = DApp f (identity <$> as) 
  describe (BVar x)     = DVar x
  identify i            = go 
    where
      go (BApp f as)    = App i f as
      go (BVar x)       = Var i x

  cache = termCache

identity :: Term -> Id
identity (App i _ _)   = i
identity (Var i _)     = i

instance Uninternable Term where
  unintern (App _ f as)  = BApp f as
  unintern (Var _ x)     = BVar x

termCache :: Cache Term
termCache = mkCache
{-# NOINLINE termCache #-}

instance Eq (Description Term) where
  DApp f as    == DApp f' as'    = f == f' && as == as'
  DVar x       == DVar x'       = x == x'
  _            == _             = False

instance Hashable (Description Term) where
  hashWithSalt s (DApp f a)   = s `hashWithSalt` (0 :: Int) `hashWithSalt` f `hashWithSalt` a
  hashWithSalt s (DVar n)     = s `hashWithSalt` (3 :: Int) `hashWithSalt` n

instance Eq Term where
  (==) = (==) `on` identity

instance Ord Term where
  compare = compare `on` identity

