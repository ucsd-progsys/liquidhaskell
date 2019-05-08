
-------------------------------------------------------------------------------
-- | This module formalizes the key datatypes needed to represent Horn NNF 
--   constraints as described in "Local Refinement Typing", ICFP 2017
-------------------------------------------------------------------------------

{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveTraversable          #-}

module Language.Fixpoint.Horn.Types 
  ( -- * Horn Constraints and their components
    Query (..)
  , Cstr  (..)
  , Pred  (..)
  , Bind  (..)
  , Var   (..) 

    -- * accessing constraint labels
  , cLabel

    -- * invariants (refinements) on constraints 
  , okCstr 
  , dummyBind
  ) 
  where 

import           Data.Generics             (Data)
import           Data.Typeable             (Typeable)
import           GHC.Generics              (Generic)
import qualified Language.Fixpoint.Types as F
import qualified Text.PrettyPrint.HughesPJ.Compat as P
import qualified Data.HashMap.Strict as M

-------------------------------------------------------------------------------
-- | @HVar@ is a Horn variable 
-------------------------------------------------------------------------------
data Var a = HVar
  { hvName :: !F.Symbol                         -- ^ name of the variable $k1, $k2 etc.
  , hvArgs :: ![F.Sort] {- len hvArgs > 0 -}    -- ^ sorts of its parameters i.e. of the relation defined by the @HVar@
  , hvMeta :: a                                 -- ^ meta-data
  }
  deriving (Eq, Ord, Data, Typeable, Generic, Functor)

-------------------------------------------------------------------------------
-- | @HPred@ is a Horn predicate that appears as LHS (body) or RHS (head) of constraints 
-------------------------------------------------------------------------------
data Pred 
  = Reft  !F.Expr                               -- ^ r 
  | Var   !F.Symbol ![F.Symbol]                 -- ^ $k(y1..yn) 
  | PAnd  ![Pred]                               -- ^ p1 /\ .../\ pn 
  deriving (Data, Typeable, Generic, Eq)
   
-------------------------------------------------------------------------------
-- | @Cst@ is an NNF Horn Constraint. 
-------------------------------------------------------------------------------
-- Note that a @Bind@ is a simplified @F.SortedReft@ ...
data Bind = Bind 
  { bSym  :: !F.Symbol 
  , bSort :: !F.Sort 
  , bPred :: !Pred 
  }
  deriving (Data, Typeable, Generic, Eq)

dummyBind :: Bind 
dummyBind = Bind F.dummySymbol F.intSort (PAnd []) 

-- Can we enforce the invariant that CAnd has len > 1?
data Cstr a
  = Head  !Pred a               -- ^ p
  | CAnd  ![(Cstr a)]           -- ^ c1 /\ ... /\ cn
  | All   !Bind  !(Cstr a)      -- ^ \all x:t. p => c
  | Any   !Bind  !(Cstr a)      -- ^ \exi x:t. p => c
  deriving (Data, Typeable, Generic, Functor, Eq)

cLabel :: Cstr a -> a
cLabel (Head _ l)   = l
cLabel (CAnd (c:_)) = cLabel c
cLabel (CAnd [])    = F.panic ("Empty Horn conjunction!") 
cLabel (All _ c)    = cLabel c 
cLabel (Any _ c)    = cLabel c

-- We want all valid constraints to start with a binding at the top
okCstr :: Cstr a -> Bool 
okCstr (All {}) = True 
okCstr (Any {}) = True 
okCstr _        = False 

-------------------------------------------------------------------------------
-- | @Query@ is an NNF Horn Constraint. 
-------------------------------------------------------------------------------

data Query a = Query 
  { qQuals :: ![F.Qualifier]                    -- ^ qualifiers over which to solve cstrs
  , qVars  :: ![Var a]                          -- ^ kvars, with parameter-sorts
  , qCstr  :: !(Cstr a)                         -- ^ list of constraints
  , qCon   :: M.HashMap (F.Symbol) (F.Sort)     -- ^ list of constants (uninterpreted functions
  , qDis   :: M.HashMap (F.Symbol) (F.Sort)     -- ^ list of constants (uninterpreted functions
  }
  deriving (Data, Typeable, Generic, Functor)


-------------------------------------------------------------------------------
-- Pretty Printing
-------------------------------------------------------------------------------
parens :: String -> String
parens s = "(" ++ s ++ ")"

instance Show (Var a) where
  show (HVar k xs _) = show k ++ parens (unwords (show <$> xs))

instance Show Pred where
  show (Reft p) = parens $ F.showpp p
  show (Var x xs) = parens $ unwords (F.symbolString <$> x:xs)
  show (PAnd ps) = parens $ unwords $ "and": map show ps

instance Show (Cstr a) where
  show (Head p _) = parens $ show p
  show (All b c) = parens $ unwords ["forall" , show b , show c]
  show (Any b c) = parens $ unwords ["exists" , show b , show c]
  show (CAnd cs) = parens $ unwords $ "and" : map show cs

instance Show Bind where
  show (Bind x t p) = parens $ unwords [parens $ unwords [F.symbolString x, F.showpp t], show p]

instance F.PPrint (Var a) where
  pprintPrec _ _ v = P.ptext $ show v

instance F.PPrint Pred where
  pprintPrec k t (Reft p) = P.parens $ F.pprintPrec k t p
  pprintPrec _ _ (Var x xs) = P.parens $ P.hsep (P.ptext . F.symbolString <$> x:xs)
  pprintPrec k t (PAnd ps) = P.parens $ P.vcat $ P.ptext "and" : map (F.pprintPrec (k+2) t) ps

instance F.PPrint (Cstr a) where
  pprintPrec k t (Head p _) = P.parens $ F.pprintPrec k t p
  pprintPrec k t (All b c) =
    P.parens $ P.vcat [P.ptext "forall" P.<+> F.pprintPrec (k+2) t b, F.pprintPrec (k+1) t c]
  pprintPrec k t (Any b c) =
    P.parens $ P.vcat [P.ptext "exists" P.<+> F.pprintPrec (k+2) t b, F.pprintPrec (k+1) t c]
  pprintPrec k t (CAnd cs) = P.parens $ P.vcat  $ P.ptext "and" : map (F.pprintPrec (k+2) t) cs

instance F.PPrint Bind where
  pprintPrec _ _ b = P.ptext $ show b
