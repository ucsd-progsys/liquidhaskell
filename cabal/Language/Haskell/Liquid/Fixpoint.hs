{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, UndecidableInstances #-}

module Language.Haskell.Liquid.Fixpoint (
    toFixpoint, toFix
  , dummySort
  , symChars, nonSymbol, dummySymbol, intSymbol, tagSymbol, tempSymbol
  , anfPrefix, tempPrefix
  , intKvar
  , Sort (..), Symbol (..), Loc (..), Constant (..), Bop (..), Brel (..), Expr (..)
  , Pred (..), Refa (..), SortedReft (..), Reft(..), Envt
  , SubC (..), WfC(..), FixResult (..), FixSolution, FInfo (..)
  , emptyFEnv, fromListFEnv, insertFEnv, deleteFEnv
  , vv
  , meet
  , trueReft, trueSortedReft 
  , canonReft, exprReft, symbolReft
  , isNonTrivialSortedReft
  , isTauto, flattenRefas
  -- , hasTag
  , symbolStr
  , simplify
  , emptySubst, mkSubst, catSubst
  , Subable (..)
  ) where

import Outputable
import Control.Monad.State
import Text.Printf
import Data.Monoid
import Data.Functor
import Data.List
import Data.Char        (isAlphaNum, isAlpha)
import qualified Data.Map as M
import qualified Data.Set as S
import Text.Parsec.String

import Data.Generics.Schemes
import Data.Generics.Aliases
import Data.Data


import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.FileNames

import qualified Data.Text as T

import Control.DeepSeq

-- type Output = SDoc -- T.Text

class Fixpoint a where
  toFix    :: a -> SDoc

  simplify :: a -> a 
  simplify =  id

------------------------------------------------------------
------------------- Sanitizing Symbols ---------------------
------------------------------------------------------------

data FxInfo = FxInfo { 
    symMap     :: !(M.Map Symbol Symbol)
  , constants  :: !(S.Set (Symbol, Sort, Bool))  -- Bool : whether to generate qualifiers for constant 
  , locMap     :: !(M.Map Loc Loc) 
  , freshIdx   :: !Integer }

type Fx     = State FxInfo

cleanLocs    :: (Data a) => a -> Fx a
cleanLocs = everywhereM (mkM swiz)
  where swiz l@(FLoc x)
          | isFixSym x = return l
          | otherwise  = freshLoc l  
        swiz l = return l

freshLoc ::  Loc -> Fx Loc
freshLoc x 
  = do s <- get
       case M.lookup x $ locMap s of
         Nothing -> do let n = freshIdx s 
                       let y = {-traceShow ("freshLoc " ++ (show x)) $ -} FLoc ("ty_" ++ show n) 
                       put $ s {freshIdx = n + 1} { locMap = M.insert x y $ locMap s}
                       return y 
         Just y  -> return y

cleanSymbols :: (Data a) => a -> Fx a
cleanSymbols = everywhereM (mkM swiz)
  where swiz s@(S x) 
          | isFixSym x = return s
          | otherwise  = freshSym s

freshSym ::  Symbol -> Fx Symbol
freshSym x = do 
  s <- get
  case M.lookup x $ symMap s of
    Nothing -> do let n = freshIdx s
                  let y = tempSymbol "fx" n 
                  put $ s {freshIdx = n + 1} { symMap = M.insert x y $ symMap s}
                  return y 
    Just y  -> return y

getConstants :: (Data a) => a -> [(Symbol, Sort, Bool)]
getConstants = everything (++) ([] `mkQ` f)
  where f (EDat s so) = [(s, so, True)]
        f (ELit s so) = [(s, so, False)]
        f _           = []

infoConstant (c, so, b)
  | b 
  = vcat [d1, d2, d3] $+$ dn
  | otherwise 
  = d1 $+$ dn 
  where d1 = text "constant" <+> d <+> text ":" <+> toFix so  
        dn = text "\n\n" 
        d  = toFix c
        d2 = text "qualif TEQ" <> d <> text "(v:ptr) : (" <> tg <> text "([v]) =  " <> d <> text ")" 
        d3 = text "qualif TNE" <> d <> text "(v:ptr) : (" <> tg <> text "([v]) !=  " <> d <> text ")" 
        tg = text tagName

---------------------------------------------------------------
---------- Converting Constraints to Fixpoint Input -----------
---------------------------------------------------------------

instance Fixpoint a => Fixpoint [a] where
  toFix xs = brackets $ sep $ punctuate (text ";") (fmap toFix xs)
  simplify = map simplify

instance (Fixpoint a, Fixpoint b) => Fixpoint (a,b) where
  toFix   (x,y)  = (toFix x) <+> text ":" <+> (toFix y)
  simplify (x,y) = (simplify x, simplify y) 

data FInfo a = FI { cs :: ![SubC a]
                  , ws :: ![WfC a ] 
                  , gs :: !Envt --[(Symbol, Sort)] 
                  } deriving (Data, Typeable)

--toFixpoint :: (Data a, Data b) => ([(Symbol, SortedReft)], ([SubC a], [WfC b])) -> (SDoc, Subst) 
toFixpoint :: (Data a) => FInfo a -> (SDoc, Subst) 
toFixpoint x = (gsDoc x' $+$ conDoc x' $+$  csDoc x' $+$ wsDoc x', sub st') 
  where (x', st')  = runState (clean x) $ FxInfo M.empty S.empty M.empty 0
        conDoc     = vcat . map infoConstant . S.elems . S.fromList . getConstants 
        csDoc      = vcat . map toFix . cs 
        wsDoc      = vcat . map toFix . ws 
        gsDoc      = vcat . map infoConstant . map (\(x, (RR so _)) -> (x, so, False)) . M.assocs . (\(Envt e) -> e) . gs
        sub        = Su . M.map EVar . symMap 
        clean      = cleanSymbols >=> cleanLocs

---------------------------------------------------------------
------------------------------ Sorts --------------------------
---------------------------------------------------------------

data Loc  = FLoc !String 
          | FLvar !Int 
	      deriving (Eq, Ord, Data, Typeable, Show)

data Sort = FInt 
          | FBool
          | FNum                 -- numeric kind for Num tyvars
          | FObj                 -- uninterpreted type
          | FVar  !Int           -- fixpoint type variable
          | FPtr  !Loc           -- haskell  type variable
          | FFunc !Int ![Sort]   -- type-var arity, in-ts ++ [out-t]
	      deriving (Eq, Ord, Data, Typeable, Show)

newtype Sub = Sub [(Int, Sort)]


-- Serializers
instance Fixpoint Loc where 
  toFix (FLoc s)  = text s
  toFix (FLvar i) = toFix i
 
pprShow = text . show 

instance Fixpoint Sort where
  toFix (FVar i)     =  text "@"   <> parens (ppr i)
  toFix (FPtr l)     =  text "ptr" <> parens (toFix l)
  toFix FInt         =  text "int"
  toFix FBool        =  text "bool"
  toFix FObj         =  text "obj"
  toFix FNum         =  text "num"
  toFix (FFunc n ts) =  text "func" <> parens ((ppr n) <> (text ", ") <> (toFix ts))


---------------------------------------------------------------
---------------------------- Symbols --------------------------
---------------------------------------------------------------

symChars 
  =  ['a' .. 'z'] 
  ++ ['A' .. 'Z'] 
  ++ ['0' .. '9'] 
  ++ ['_', '%', '.', '#', '$']

newtype Symbol = S String 
                 deriving (Eq, Ord, Data, Typeable)

instance Fixpoint Symbol where
  toFix (S x) = text x

instance Outputable Symbol where
  ppr = toFix 


instance Show Symbol where
  show (S x) = x


newtype Subst  = Su (M.Map Symbol Expr) 
                 deriving (Eq, Ord, Data, Typeable)

instance Fixpoint Subst where
  toFix (Su m) = case M.toAscList m of 
                   []  -> empty
                   xys -> hcat $ map (\(x,y) -> brackets $ (toFix x) <> text ":=" <> (toFix y)) xys

isFixSym (c:cs) = isAlpha c && all (`elem` symChars) cs
isFixSym _      = False

of_string               = S
vv                      = S "VV" --vvPrefix --S . (vvPrefix ++) . to_string_short 
dummySymbol             = S dummyName
tagSymbol               = S tagName

-- Bogus type for hs values that cannot be embedded into Fixpoint
dummySort               = FFunc 0 [FObj]

intSymbol x i           = S $ x ++ show i           

tempSymbol              ::  String -> Integer -> Symbol
tempSymbol prefix n     = intSymbol (tempPrefix ++ prefix) n




isTempSym (S x)         = tempPrefix `isPrefixOf` x
tempPrefix              = "lq#tmp#"
anfPrefix               = "lq#anf#" 
-- vvPrefix                = "VV_"
nonSymbol               = S ""

intKvar                 :: Integer -> Symbol
intKvar                 = intSymbol "k_" 

---------------------------------------------------------------
------------------------- Expressions -------------------------
---------------------------------------------------------------

data Constant = I !Integer 
              deriving (Eq, Ord, Data, Typeable, Show)

data Brel = Eq | Ne | Gt | Ge | Lt | Le 
            deriving (Eq, Ord, Data, Typeable, Show)

data Bop  = Plus | Minus | Times | Div | Mod    
            deriving (Eq, Ord, Data, Typeable, Show)
	    -- NOTE: For "Mod" 2nd expr should be a constant or a var *)

data Expr = ECon !Constant 
          | EVar !Symbol
          | EDat !Symbol !Sort
          | ELit !Symbol !Sort
          | EApp !Symbol ![Expr]
          | EBin !Bop !Expr !Expr
          | EIte !Pred !Expr !Expr
          | ECst !Expr !Sort
          | EBot
          deriving (Eq, Ord, Data, Typeable, Show)

instance Fixpoint Integer where
  toFix = pprShow 

instance Fixpoint Constant where
  toFix (I i) = pprShow i


instance Fixpoint Brel where
  toFix Eq = text "="
  toFix Ne = text "!="
  toFix Gt = text ">"
  toFix Ge = text ">="
  toFix Lt = text "<"
  toFix Le = text "<="

instance Fixpoint Bop where
  toFix Plus  = text "+"
  toFix Minus = text "-"
  toFix Times = text "*"
  toFix Div   = text "/"
  toFix Mod   = text "mod"

instance Fixpoint Expr where
  toFix (ECon c)       = toFix c 
  toFix (EVar s)       = toFix s
  toFix (EDat s _)     = toFix s 
  toFix (ELit s _)     = toFix s
  toFix (EApp f es)    = (toFix f) <> (parens $ toFix es) 
  toFix (EBin o e1 e2) = parens $ toFix e1 <+> toFix o <+> toFix e2
  toFix (EIte p e1 e2) = parens $ toFix p <+> text "?" <+> toFix e1 <+> text ":" <+> toFix e2 
  toFix (ECst e so)    = parens $ toFix e <+> text " : " <+> toFix so 
  toFix (EBot)         = text "_|_"

----------------------------------------------------------
--------------------- Predicates -------------------------
----------------------------------------------------------

data Pred = PTrue
          | PFalse
          | PAnd  ![Pred]
          | POr   ![Pred]
          | PNot  !Pred
          | PImp  !Pred !Pred
          | PIff  !Pred !Pred
          | PBexp !Expr
          | PAtom !Brel !Expr !Expr
          | PAll  ![(Symbol, Sort)] !Pred
          | PTop
          deriving (Eq, Ord, Data, Typeable, Show)

--instance Fixpoint Pred where 
--  toFix PTop            = text "???"
--  toFix PTrue           = text "true"
--  toFix PFalse          = text "false"
--  toFix (PBexp e)       = printf "(Bexp %s)"   (toFix e)
--  toFix (PNot p)        = parens (text "~ " <> parens (ppr p))
--  toFix (PImp p1 p2)    = parens (ppr p1 <> text " => " <> ppr p2) 
--  toFix (PIff p1 p2)    = parens (ppr p1 <> text " <=> " <> ppr p2)
--  toFix (PAnd ps)       = text "&& " <> ppr ps
--  toFix (POr  ps)       = text "|| " <> ppr ps 
--  toFix (PAtom r e1 e2) = parens (ppr e1 <> text " " <> ppr r <> text " " <> ppr e2) 
--  toFix (PAll xts p)    = text "forall " <> ppr xts <> text " . " <> ppr p
--  toFix (PBexp e)       = ppr e 
--

instance Fixpoint Pred where
  toFix PTop            = text "???"
  toFix PTrue           = text "true"
  toFix PFalse          = text "false"
  toFix (PBexp e)       = parens $ text "?" <+> toFix e
  toFix (PNot p)        = parens $ text "~" <+> parens (toFix p)
  toFix (PImp p1 p2)    = parens $ (toFix p1) <+> text "=>" <+> (toFix p2)
  toFix (PIff p1 p2)    = parens $ (toFix p1) <+> text "<=>" <+> (toFix p2)
  toFix (PAnd ps)       = text "&&" <+> toFix ps
  toFix (POr  ps)       = text "||" <+> toFix ps
  toFix (PAtom r e1 e2) = parens $ toFix e1 <+> toFix r <+> toFix e2
  toFix (PAll xts p)    = text "forall" <+> (toFix xts) <+> text "." <+> (toFix p)

  simplify (PAnd [])    = PTrue
  simplify (POr  [])    = PFalse
  simplify (PAnd [p])   = simplify p
  simplify (POr  [p])   = simplify p
  simplify (PAnd ps)    
    | any isContra ps   = PFalse
    | otherwise         = PAnd $ map simplify ps
  simplify (POr  ps)    
    | any isTauto ps    = PTrue
    | otherwise         = POr  $ map simplify ps 
  simplify p            
    | isContra p        = PFalse
    | isTauto  p        = PTrue
    | otherwise         = p

zero         = ECon (I 0)
one          = ECon (I 1)
isContra     = (`elem` [ PAtom Eq zero one, PAtom Eq one zero, PFalse])   
isTauto      = (`elem` [ PTrue ])
hasTag e1 e2 = PAtom Eq (EApp tagSymbol [e1]) e2



---------------------------------------------------------------
----------------- Refinements and Environments  ---------------
---------------------------------------------------------------

data Refa 
  = RConc !Pred 
  | RKvar !Symbol !Subst
  deriving (Eq, Ord, Data, Typeable)

newtype Reft 
  = Reft (Symbol, [Refa]) 
  deriving (Eq, Ord, Data, Typeable) 

instance Show Reft where
  show (Reft x) = showSDoc $ toFix x 

data SortedReft
  = RR !Sort !Reft
  deriving (Eq, Ord, Data, Typeable) 

isNonTrivialSortedReft (RR _ (Reft (_, ras)))
  = not $ null ras

meet ::  Reft -> Reft -> Reft
meet (Reft (v, ras)) (Reft (v', ras')) 
  | v == v'   = Reft (v, ras ++ ras')
  | otherwise = Reft (v, ras ++ (ras' `subst1` (v', EVar v)))

newtype Envt = Envt (M.Map Symbol SortedReft) 
               deriving (Eq, Ord, Data, Typeable) 
  
instance Fixpoint Refa where
  toFix (RConc p)    = toFix p
  toFix (RKvar k su) = toFix k <> toFix su

instance Fixpoint SortedReft where
  toFix (RR so (Reft (v, ras))) 
    = braces 
    $ (toFix v) <+> (text ":") <+> (toFix so) <+> (text "|") <+> toFix ras

instance Fixpoint Envt where
  toFix (Envt m)  = toFix (M.toAscList m)

insertFEnv ::  Symbol -> SortedReft -> Envt -> Envt
insertFEnv x r (Envt m) = Envt (M.insert x r m)
deleteFEnv x (Envt m)   = Envt (M.delete x m)
fromListFEnv            = Envt . M.fromList . (builtins ++) 
  where builtins        = [(tagSymbol, trueSortedReft $ FFunc 1 [FVar 0, FObj])]
emptyFEnv               = Envt M.empty

---------------------------------------------------------------
----------------- Refinements and Environments  ---------------
---------------------------------------------------------------

data SubC a = SubC { senv  :: !Envt
                   , sgrd  :: !Pred
                   , slhs  :: !SortedReft
                   , srhs  :: !SortedReft
                   , sid   :: !(Maybe Integer)
                   , stag  :: ![Int] 
                   , sinfo :: !a
                   } deriving (Eq, Ord, Data, Typeable)

data WfC a  = WfC  { wenv  :: !Envt
                   , wrft  :: !SortedReft
                   , wid   :: !(Maybe Integer) 
                   , winfo :: !a
                   } deriving (Eq, Ord, Data, Typeable)

data FixResult a = Crash | Safe | Unsafe ![a]

type FixSolution = M.Map Symbol Pred

instance Monoid (FixResult a) where
  mempty = Safe
  mappend Safe x  = x
  mappend x Safe  = x
  mappend _ Crash = Crash
  mappend Crash _ = Crash
  mappend (Unsafe xs) (Unsafe ys) = Unsafe (xs ++ ys)

instance Outputable a => Outputable (FixResult (SubC a)) where
  ppr Crash       = text "Crash! "
  ppr Safe        = text "Safe"
  ppr (Unsafe xs) = text "Unsafe: " <> ppr (sinfo `fmap` xs)

--instance Fixpoint SortedReft where
--  toFix (RR so (Reft (v, ras))) 
--    = printf "{%s : %s | %s}" (toFix v) (toFix so) (toFix ras)
--
--instance Fixpoint (SubC a) where 
--  toFix c = printf "constraint: \n  env  %s  \n  grd %s  \n  lhs %s \n  rhs %s \n  %s %s \n\n\n"
--              se sg sl sr (ppid $ sid c) (pptag $ stag c)
--    where se = toFix $ senv c 
--          sg = toFix $ sgrd c 
--          sl = toFix $ slhs c 
--          sr = toFix $ srhs c
--
--instance Outputable (WfC a) where 
--  toFix w = printf "wf: \n  env  %s  \n  reft %s \n  %s \n" se sr (ppid $ wid w)
--    where se = toFix $ wenv w
--          sr = toFix $ wrft w

--instance Fixpoint (WfC a) where 
--  toFix w = printf "wf: \n  env  %s  \n  reft %s \n  %s \n" se sr (ppid $ wid w)
--    where se = toFix $ wenv w
--          sr = toFix $ wrft w

toFixPfx s x     = text s <+> toFix x

instance Outputable (SubC a) where
  ppr = toFix 

instance Outputable (WfC a) where
  ppr = toFix 

instance Fixpoint (SubC a) where
  toFix c     = hang (text "\n\nconstraint:") 2 bd
     where bd =   text "env" <+> toFix (senv c) 
              $+$ text "grd" <+> toFix (sgrd c) 
              $+$ text "lhs" <+> toFix (slhs c) 
              $+$ text "rhs" <+> toFix (srhs c)
              $+$ (pprId (sid c) <+> pprTag (stag c)) 

instance Fixpoint (WfC a) where 
  toFix w     = hang (text "\n\nwf:") 2 bd 
    where bd  =   text "env"  <+> toFix (wenv w)
              $+$ text "reft" <+> toFix (wrft w) 
              $+$ pprId (wid w)

pprId (Just i)  = text "id" <+> (text $ show i)
pprId _         = text ""

pprTag []       = text ""
pprTag is       = text "tag" <+> toFix is 

instance Fixpoint Int where
  toFix = ppr


-------------------------------------------------------
------------------- Substitutions ---------------------
-------------------------------------------------------

class Subable a where
  subst  :: Subst -> a -> a
  
  subst1 :: a -> (Symbol, Expr) -> a
  subst1 thing (x, e) = subst (Su $ M.singleton x e) thing


instance Subable Expr where
  subst su (EApp f es)     = EApp f $ map (subst su) es 
  subst su (EBin op e1 e2) = EBin op (subst su e1) (subst su e2)
  subst su (EIte p e1 e2)  = EIte (subst su p) (subst su e1) (subst  su e2)
  subst su (ECst e so)     = ECst (subst su e) so
  subst (Su s) e@(EVar x)  = M.findWithDefault e x s
  subst su e               = e

instance Subable Pred where
  subst su (PAnd ps)       = PAnd $ map (subst su) ps
  subst su (POr  ps)       = POr  $ map (subst su) ps
  subst su (PNot p)        = PNot $ subst su p
  subst su (PImp p1 p2)    = PImp (subst su p1) (subst su p2)
  subst su (PIff p1 p2)    = PIff (subst su p1) (subst su p2)
  subst su (PBexp e)       = PBexp $ subst su e
  subst su (PAtom r e1 e2) = PAtom r (subst su e1) (subst su e2)
  subst su p@(PAll _ _)    = error $ "subst: FORALL" 
  subst su p               = p

instance Subable Refa where
  subst su (RConc p)       = RConc   $ subst su p
  subst su (RKvar k su')   = RKvar k $ su' `catSubst` su 

instance (Subable a, Subable b) => Subable (a,b) where
  subst su (x,y) = (subst su x, subst su y)

instance Subable a => Subable [a] where
  subst su = map $ subst su

instance Subable a => Subable (M.Map k a) where
  subst su = M.map $ subst su

instance Subable Reft where
  subst su (Reft (v, ras)) = Reft (v, subst su ras)

instance Subable SortedReft where
  subst su (RR so r) = RR so $ subst su r

emptySubst 
  = Su M.empty

catSubst (Su s1) (Su s2) 
  = Su $ s1' `M.union` s2
    where s1' = subst (Su s2) `M.map` s1

mkSubst = Su . M.fromList

------------------------------------------------------------
------------- Generally Useful Refinements -----------------
------------------------------------------------------------

symbolReft = exprReft . EVar 
exprReft e = Reft (vv, [RConc $ PAtom Eq (EVar vv) e])

trueSortedReft :: Sort -> SortedReft
trueSortedReft = (`RR` trueReft) 

trueReft :: Reft
trueReft = Reft (vv, [])

canonReft :: Reft -> Reft
canonReft r@(Reft (v, ras)) 
  | v == vv    = r 
  | otherwise = Reft (vv, ras `subst1` (v, EVar vv))

flattenRefas = concatMap flatRa
  where flatRa (RConc p) = RConc <$> flatP p
        flatRa ra        = [ra]
        flatP  (PAnd ps) = concatMap flatP ps
        flatP  p         = [p]

symbolStr (S x) = x



----------------------------------------------------------------
---------------------- Strictness ------------------------------
----------------------------------------------------------------
instance NFData Symbol where
  rnf (S x) = rnf x

instance NFData Loc where
  rnf (FLoc x) = rnf x
  rnf (FLvar x) = rnf x

instance NFData Sort where
  rnf (FVar x)     = rnf x
  rnf (FPtr x)     = rnf x
  rnf (FFunc n ts) = rnf n `seq` (map rnf ts) `seq` () 
  rnf (z)          = z `seq` ()

instance NFData Sub where
  rnf (Sub x) = rnf x

instance NFData Subst where
  rnf (Su x) = rnf x

instance NFData Envt where
  rnf (Envt x) = rnf x

instance NFData Constant where
  rnf (I x) = rnf x

instance NFData Brel 
instance NFData Bop

instance NFData Expr where
  rnf (ECon x)        = rnf x
  rnf (EVar x)        = rnf x
  rnf (EDat x1 x2)    = rnf x1 `seq` rnf x2
  rnf (ELit x1 x2)    = rnf x1 `seq` rnf x2
  rnf (EApp x1 x2)    = rnf x1 `seq` rnf x2
  rnf (EBin x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3
  rnf (EIte x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3
  rnf (ECst x1 x2)    = rnf x1 `seq` rnf x2
  rnf (_)             = ()

instance NFData Pred where
  rnf (PAnd x)         = rnf x
  rnf (POr  x)         = rnf x
  rnf (PNot x)         = rnf x
  rnf (PBexp x)        = rnf x
  rnf (PImp x1 x2)     = rnf x1 `seq` rnf x2
  rnf (PIff x1 x2)     = rnf x1 `seq` rnf x2
  rnf (PAll x1 x2)     = rnf x1 `seq` rnf x2
  rnf (PAtom x1 x2 x3) = rnf x1 `seq` rnf x2 `seq` rnf x3
  rnf (_)              = ()

instance NFData Refa where
  rnf (RConc x)     = rnf x
  rnf (RKvar x1 x2) = rnf x1 `seq` rnf x2

instance NFData Reft where 
  rnf (Reft (v, ras)) = rnf v `seq` rnf ras

instance NFData SortedReft where 
  rnf (RR so r) = rnf so `seq` rnf r

instance (NFData a) => NFData (SubC a) where
  rnf (SubC x1 x2 x3 x4 x5 x6 x7) 
    = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4 `seq` rnf x5 `seq` rnf x6 `seq` rnf x7

instance (NFData a) => NFData (WfC a) where
  rnf (WfC x1 x2 x3 x4) 
    = rnf x1 `seq` rnf x2 `seq` rnf x3 `seq` rnf x4





