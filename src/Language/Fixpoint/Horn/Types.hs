
-------------------------------------------------------------------------------
-- | This module formalizes the key datatypes needed to represent Horn NNF 
--   constraints as described in "Local Refinement Typing", ICFP 2017
-------------------------------------------------------------------------------

{-# LANGUAGE OverloadedStrings          #-}
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

    -- * Raw Query
  , Tag (..)
  , TagVar
  , TagQuery 

    -- * accessing constraint labels
  , cLabel

    -- * invariants (refinements) on constraints 
  , okCstr 
  , dummyBind

    -- * extract qualifiers 
  , quals
  ) 
  where 

import           Data.Generics             (Data)
import           Data.Typeable             (Typeable)
import           GHC.Generics              (Generic)
import           Control.DeepSeq ( NFData )
import qualified Data.Text               as T
import           Data.Maybe (fromMaybe)
import qualified Data.List               as L
import qualified Language.Fixpoint.Misc  as Misc
import qualified Language.Fixpoint.Types as F
import qualified Text.PrettyPrint.HughesPJ.Compat as P
import qualified Data.HashMap.Strict as M
import           Data.Aeson

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


instance Semigroup Pred where
  p1 <> p2 = PAnd [p1, p2]

instance Monoid Pred where 
  mempty = Reft mempty

instance F.Subable Pred where
  syms (Reft e)   = F.syms e
  syms (Var _ xs) = xs
  syms (PAnd ps)  = concatMap F.syms ps

  substa f (Reft e)   = Reft  (F.substa f      e)
  substa f (Var k xs) = Var k (F.substa f <$> xs)
  substa f (PAnd ps)  = PAnd  (F.substa f <$> ps)

  subst su (Reft  e)  = Reft  (F.subst su      e)
  subst su (PAnd  ps) = PAnd  (F.subst su <$> ps)
  subst su (Var k xs) = Var k (F.subst su <$> xs)

  substf f (Reft  e)  = Reft  (F.substf f      e)
  substf f (PAnd  ps) = PAnd  (F.substf f <$> ps)
  substf f (Var k xs) = Var k (F.substf f <$> xs)

  subst1 (Reft  e)  su = Reft  (F.subst1 e su)
  subst1 (PAnd  ps) su = PAnd  [F.subst1 p su | p <- ps]
  subst1 (Var k xs) su = Var k [F.subst1 x su | x <- xs]

-------------------------------------------------------------------------------
quals :: Cstr a -> [F.Qualifier] 
-------------------------------------------------------------------------------
quals = F.tracepp "horn.quals" . cstrQuals F.emptySEnv F.vv_  

cstrQuals :: F.SEnv F.Sort -> F.Symbol -> Cstr a -> [F.Qualifier] 
cstrQuals = go 
  where
    go env v (Head p _)  = predQuals env v p
    go env v (CAnd   cs) = concatMap (go env v) cs
    go env _ (All  b c)  = bindQuals env b c 
    go env _ (Any  b c)  = bindQuals env b c

bindQuals  :: F.SEnv F.Sort -> Bind -> Cstr a -> [F.Qualifier] 
bindQuals env b c = predQuals env' bx (bPred b) ++ cstrQuals env' bx c 
  where 
    env'          = F.insertSEnv bx bt env
    bx            = bSym b
    bt            = bSort b

predQuals :: F.SEnv F.Sort -> F.Symbol -> Pred -> [F.Qualifier]
predQuals env v (Reft p)  = exprQuals env v p
predQuals env v (PAnd ps) = concatMap (predQuals env v) ps
predQuals _   _ _         = [] 

exprQuals :: F.SEnv F.Sort -> F.Symbol -> F.Expr -> [F.Qualifier]
exprQuals env v e = mkQual env v <$> F.conjuncts e

mkQual :: F.SEnv F.Sort -> F.Symbol -> F.Expr -> F.Qualifier
mkQual env v p = case envSort env <$> (v:xs) of
                   (_,so):xts -> F.mkQ "Auto" ((v, so) : xts) p junk 
                   _          -> F.panic "impossible"
  where
    xs         = L.delete v $ Misc.hashNub (F.syms p)
    junk       = F.dummyPos "mkQual" 

envSort :: F.SEnv F.Sort -> F.Symbol -> (F.Symbol, F.Sort)
envSort env x = case F.lookupSEnv x env of
                   Just t -> (x, t) 
                   _      -> F.panic $ "unbound symbol in scrape: " ++ F.showpp x
{- 
  | Just _ <- lookupSEnv x lEnv = Nothing
  | otherwise                   = Just (x, ai)
  where
    ai             = trace msg $ fObj $ Loc l l $ tempSymbol "LHTV" i
    msg            = "Unknown symbol in qualifier: " ++ show x
-}


--------------------------------------------------------------------------------
-- | @Cst@ is an NNF Horn Constraint. 
-------------------------------------------------------------------------------
-- Note that a @Bind@ is a simplified @F.SortedReft@ ...
data Bind = Bind 
  { bSym  :: !F.Symbol 
  , bSort :: !F.Sort 
  , bPred :: !Pred 
  }
  deriving (Data, Typeable, Generic, Eq)

instance F.Subable Bind where
    syms = undefined
    substa = undefined
    substf = undefined
    subst su (Bind x t p) = (Bind x t (F.subst su p))

dummyBind :: Bind 
dummyBind = Bind F.dummySymbol F.intSort (PAnd []) 

-- Can we enforce the invariant that CAnd has len > 1?
data Cstr a
  = Head  !Pred a               -- ^ p
  | CAnd  ![(Cstr a)]           -- ^ c1 /\ ... /\ cn
  | All   !Bind  !(Cstr a)      -- ^ \all x:t. p => c
  | Any   !Bind  !(Cstr a)      -- ^ \exi x:t. p /\ c or is it \exi x:t. p => c?
  deriving (Data, Typeable, Generic, Functor, Eq)

cLabel :: Cstr a -> a
cLabel cstr = case go cstr of
  [] -> F.panic "everything is true!!!"
  label:_ -> label
  where
    go (Head _ l)   = [l]
    go (CAnd cs)    = mconcat $ go <$> cs
    go (All _ c)    = go c
    go (Any _ c)    = go c

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
  , qEqns  :: ![F.Equation]                     -- ^ list of equations
  , qMats  :: ![F.Rewrite]                      -- ^ list of match-es
  , qData  :: ![F.DataDecl]                     -- ^ list of data-declarations
  }
  deriving (Data, Typeable, Generic, Functor)

-- | Tag each query with a possible string denoting "provenance"

type TagVar   = Var Tag
type TagQuery = Query Tag
data Tag      = NoTag | Tag String
  deriving (Data, Typeable, Generic, Show) 

instance NFData Tag

instance F.Loc Tag where
  srcSpan _ = F.dummySpan

instance F.Fixpoint Tag where
  toFix NoTag   = "\"\"" 
  toFix (Tag s) = "\"" <> P.text s <> "\""
  
instance F.PPrint Tag where
  pprintPrec _ _ NoTag   = mempty
  pprintPrec _ _ (Tag s) = P.ptext s 

instance ToJSON Tag where
  toJSON NoTag   = Null
  toJSON (Tag s) = String (T.pack s) 

instance F.PPrint (Query a) where 
  pprintPrec k t q = P.vcat $ L.intersperse " " 
    [ P.vcat   (ppQual <$> qQuals q)
    , P.vcat   [ppVar k   | k <- qVars q]
    , P.vcat   [ppCon x t | (x, t) <- M.toList (qCon q)]
    , ppThings Nothing (qEqns  q)
    , ppThings (Just "data ") (qData  q)
    , P.parens (P.vcat ["constraint", F.pprintPrec (k+2) t (qCstr q)])
    ]

ppThings :: F.PPrint a => Maybe P.Doc -> [a] -> P.Doc
ppThings pfx qs = P.vcat [ P.parens $ prefix P.<-> F.pprint q | q <- qs]
  where 
    prefix      = fromMaybe "" pfx 

ppCon :: F.Symbol -> F.Sort -> P.Doc
ppCon x t = P.parens ("constant" P.<+> F.pprint x P.<+> P.parens (F.pprint t))

ppQual :: F.Qualifier -> P.Doc
ppQual (F.Q n xts p _) =  P.parens ("qualif" P.<+> F.pprint n P.<+> ppBlanks (ppArg <$> xts) P.<+> P.parens (F.pprint p))
  where 
    ppArg qp    = F.pprint (F.qpSym qp) P.<+> P.parens (F.pprint (F.qpSort qp))

ppVar :: Var a -> P.Doc
ppVar (HVar k ts _)  = P.parens ("var" P.<+> "$" P.<-> F.pprint k P.<+> ppBlanks ((P.parens . F.pprint) <$> ts)) 

ppBlanks :: [P.Doc] -> P.Doc
ppBlanks ds = P.parens (P.hcat (L.intersperse " " ds))
-------------------------------------------------------------------------------
-- Pretty Printing
-------------------------------------------------------------------------------
parens :: String -> String
parens s = "(" ++ s ++ ")"

instance Show (Var a) where
  show (HVar k xs _) = show k ++ parens (unwords (show <$> xs))

instance Show Pred where
  show (Reft p)   = parens $ F.showpp p
  show (Var x xs) = parens $ unwords (F.symbolString <$> x:xs)
  show (PAnd ps)  = parens $ unwords $ "and": map show ps

instance Show (Cstr a) where
  show (Head p _) = parens $ show p
  show (All b c)  = parens $ unwords ["forall" , show b , show c]
  show (Any b c)  = parens $ unwords ["exists" , show b , show c]
  show (CAnd cs)  = parens $ unwords $ "and" : map show cs

instance Show Bind where
  show (Bind x t p) = parens $ unwords [parens $ unwords [F.symbolString x, F.showpp t], show p]

instance F.PPrint (Var a) where
  pprintPrec _ _ v = P.ptext $ show v

instance F.PPrint Pred where
  pprintPrec k t (Reft p)   = P.parens $ F.pprintPrec k t p
  pprintPrec _ _ (Var x xs) = P.parens $ P.hsep (P.ptext . F.symbolString <$> x:xs)
  pprintPrec k t (PAnd ps)  = P.parens $ P.vcat $ P.ptext "and" : map (F.pprintPrec (k+2) t) ps

instance F.PPrint (Cstr a) where
  pprintPrec k t (Head p _) = P.parens $ F.pprintPrec k t p
  pprintPrec k t (All b c)  = P.parens $ P.vcat [ P.ptext "forall" P.<+> F.pprintPrec (k+2) t b
                                                , F.pprintPrec (k+1) t c
                                                ]
  pprintPrec k t (Any b c)  = P.parens $ P.vcat [P.ptext "exists" P.<+> F.pprintPrec (k+2) t b
                                                , F.pprintPrec (k+1) t c
                                                ]
  pprintPrec k t (CAnd cs) = P.parens $ P.vcat  $ P.ptext "and" : map (F.pprintPrec (k+2) t) cs

instance F.PPrint Bind where
  pprintPrec _ _ b = P.ptext $ show b
