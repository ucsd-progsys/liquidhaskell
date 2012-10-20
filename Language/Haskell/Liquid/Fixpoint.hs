{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, UndecidableInstances #-}

-- | This module contains the data types, operations and serialization functions 
-- for representing Fixpoint's implication (i.e. subtyping) and well-formedness 
-- constraints in Haskell. The actual constraint solving is done by the
-- `fixpoint.native` which is written in Ocaml.

module Language.Haskell.Liquid.Fixpoint (
    toFixpoint
  , Fixpoint (toFix) 
  , typeSort, typeUniqueSymbol
  , symChars, isNonSymbol, nonSymbol, dummySymbol, intSymbol, tempSymbol --, tagSymbol 
  , qualifySymbol, stringSymbol, symbolString, stringSymbolRaw
  , FTycon, stringFTycon, intFTyCon, boolFTyCon
  , anfPrefix, tempPrefix
  , intKvar
  , Sort (..), Symbol(..), Constant (..), Bop (..), Brel (..), Expr (..)
  , Pred (..), Refa (..), SortedReft (..), Reft(..)
  , SEnv (..)
  , FEnv
  , SubC (..), WfC(..), FixResult (..), FixSolution, FInfo (..)
  , emptySEnv, fromListSEnv, insertSEnv, deleteSEnv, memberSEnv, lookupSEnv
  , insertFEnv 
  , vv
  , trueSortedReft 
  , trueRefa
  , canonReft, exprReft, notExprReft, symbolReft
  , isFunctionSortedReft, isNonTrivialSortedReft, isTautoReft, isSingletonReft
  , ppr_reft, ppr_reft_pred, flattenRefas
  , simplify, pAnd, pOr, pIte
  , isTautoPred
  , emptySubst, mkSubst, catSubst
  , Subable (..)
  , TCEmb (..)

  -- * Visitors
  , getSymbols
  ) where

import TypeRep 
import PrelNames            (intTyConKey, intPrimTyConKey, integerTyConKey, boolTyConKey)

import TysWiredIn           (listTyCon)
import TyCon                (TyCon, isTupleTyCon, tyConUnique)
import Outputable
import Data.Monoid hiding   ((<>))
import Data.Functor
import Data.Char            (ord, chr, isAlpha, isUpper, toLower)
import Data.List            (sort)
import qualified Data.Map as M
import qualified Data.Set as S

import Data.Generics.Schemes
import Data.Generics.Aliases
import Data.Data    hiding  (TyCon, tyConName)
import Data.Maybe           (fromMaybe)

import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.FileNames
import Language.Haskell.Liquid.GhcMisc
import Control.DeepSeq

class Fixpoint a where
  toFix    :: a -> SDoc

  simplify :: a -> a 
  simplify =  id

type TCEmb a    = M.Map a FTycon  

------------------------------------------------------------
------------------- Sanitizing Symbols ---------------------
------------------------------------------------------------
--
-- data FxInfo = FxInfo { 
--     symMap     :: !(M.Map Symbol Symbol)
--   , constants  :: !(S.Set (Symbol, Sort, Bool))  -- Bool : whether to generate qualifiers for constant 
--   , locMap     :: !(M.Map Loc Loc) 
--   , freshIdx   :: !Integer }
-- 
-- type Fx     = State FxInfo
-- 
-- cleanLocs    :: (Data a) => a -> Fx a
-- cleanLocs = {-# SCC "CleanLocs" #-} everywhereM (mkM swiz)
--   where swiz l@(FLoc x)
--           | isFixSym x = return l
--           | otherwise  = freshLoc l  
--         swiz l = return l
-- 
-- isFixSym (c:chs)  = isAlpha c && all (`elem` okSymChars) chs
-- isFixSym _        = False
-- 
-- freshLoc ::  Loc -> Fx Loc
-- freshLoc x 
--   = do s <- get
--        case M.lookup x $ locMap s of
--          Nothing -> do let n = freshIdx s 
--                        let y = FLoc ("ty_" ++ show n) 
--                        put $ s {freshIdx = n + 1} { locMap = M.insert x y $ locMap s}
--                        return y 
--          Just y  -> return y
-- 
-- cleanSymbols :: (Data a) => a -> Fx a
-- cleanSymbols = {-# SCC "CleanSyms" #-} everywhereM (mkM swiz)
--   where swiz s@(S x) 
--           | isFixSym x = return s
--           | otherwise  = freshSym s
-- 
-- freshSym ::  Symbol -> Fx Symbol
-- freshSym x = do 
--   s <- get
--   case M.lookup x $ symMap s of
--     Nothing -> do let n = freshIdx s
--                   let y = tempSymbol "fx" n 
--                   put $ s {freshIdx = n + 1} { symMap = M.insert x y $ symMap s}
--                   return y 
--     Just y  -> return y




--{{{
--strsToRefa n as = RConc $ PBexp $ (EApp (S n) ([EVar (S "VV")] ++ (map EVar as)))
--strToRefa n xs = RKvar n (Su (M.fromList xs))
--strToReft n xs = Reft (S "VV", [strToRefa n xs])
--strsToReft n as = Reft (S "VV", [strsToRefa n as])
--
--refaInReft k (Reft(v, ls)) = any (cmpRefa k) ls
--
--cmpRefa (RConc (PBexp (EApp (S n) _))) (RConc (PBexp (EApp (S n') _))) 
--  = n == n'
--cmpRefa _ _ 
--  = False
--
--replaceSorts (p, Reft(_, rs)) (Reft(v, ls))
--  = Reft(v, concatMap (replaceS (p, rs)) ls)
--
--replaceSort (p, k) (Reft(v, ls)) = Reft (v, (concatMap (replaceS (p, [k])) ls))
--
---- replaceS :: (Refa a, [Refa a]) -> Refa a -> [Refa a] 
--replaceS ((RKvar (S n) (Su s)), k) (RKvar (S n') (Su s')) 
--  | n == n'
--  = map (addSubs (Su s')) k -- [RKvar (S m) (Su (s `M.union` s1 `M.union` s'))]
--replaceS (k, v) p = [p]
--
--addSubs s ra@(RKvar k s') = RKvar k (unionTransSubs s s')
--addSubs _ f = f
--
---- union s1 s2 with transitivity : 
---- (x, z) in s1 and (z, y) in s2 => (x, y) in s
--unionTransSubs (Su s1) (Su s2) 
--  = Su $ (\(su1, su2) -> su1 `M.union` su2)(M.foldWithKey f (s1, s2) s1)
--  where f k (EVar v) (s1, s2) 
--          = case M.lookup v s2 of 
--            Just (EVar x) -> (M.adjust (\_ -> EVar x) k s1, M.delete v s2)
--            _             -> (s1, s2)
--        f _ _ s12 = s12
--
--
--
-- infoConstant (c, so, b)
--   | b 
--   = vcat [d1, d2, d3] $+$ dn
--   | otherwise 
--   = d1 $+$ dn 
--   where d1 = text "constant" <+> d <+> text ":" <+> toFix so  
--         dn = text "\n\n" 
--         d  = toFix c
--         d2 = text "qualif TEQ" <> d <> text "(v:ptr) : (" <> tg <> text "([v]) =  " <> d <> text ")" 
--         d3 = text "qualif TNE" <> d <> text "(v:ptr) : (" <> tg <> text "([v]) !=  " <> d <> text ")" 
--         tg = text tagName
-- }}}

getConstants :: (Data a) => a -> [(Symbol, Sort, Bool)]
getConstants = everything (++) ([] `mkQ` f)
  where f (EDat s so) = [(s, so, True)]
        f (ELit s so) = [(s, so, False)]
        f _           = []

getSymbols :: (Data a) => a -> [Symbol]
getSymbols = everything (++) ([] `mkQ` f)
  where f x@(S _) = [x]
        f _       = []


infoConstant (c, so, _)
  = text "constant" <+> toFix c <+> text ":" <+> toFix so <> blankLine <> blankLine 


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
                  , gs :: !FEnv -- Envt Symbol, Sort)] 
                  } deriving (Data, Typeable)

toFixpoint x' = gsDoc x' $+$ conDoc x' $+$  csDoc x' $+$ wsDoc x'
  where conDoc     = vcat . map infoConstant . S.elems . S.fromList . getConstants 
        csDoc      = vcat . map toFix . cs 
        wsDoc      = vcat . map toFix . ws 
        gsDoc      = vcat . map infoConstant . map (\(x, (RR so _)) -> (x, so, False)) . M.assocs . (\(SE e) -> e) . gs


----------------------------------------------------------------------
------------------------ Type Constructors ---------------------------
----------------------------------------------------------------------

newtype FTycon = TC Symbol deriving (Eq, Ord, Data, Typeable, Show)

intFTyCon  = TC (S "int")
boolFTyCon = TC (S "bool")
listFTyCon = TC (S listConName)

isListTC   = (listFTyCon ==)
-- isListTC (TC (S c)) = c == listConName

----------------------------------------------------------------------
------------------------------- Sorts --------------------------------
----------------------------------------------------------------------

data Sort = FInt 
          | FBool
          | FNum                 -- ^ numeric kind for Num tyvars
          | FObj  Symbol         -- ^ uninterpreted type
          | FVar  !Int           -- ^ fixpoint type variable
          | FFunc !Int ![Sort]   -- ^ type-var arity, in-ts ++ [out-t]
          | FApp FTycon [Sort]   -- ^ constructed type 
	      deriving (Eq, Ord, Data, Typeable, Show)

fApp c ts 
  | c == intFTyCon  = FInt
  | c == boolFTyCon = FBool
  | otherwise       = FApp c ts

typeSort :: TCEmb TyCon -> Type -> Sort 
-- COMMENTED OUT TO TEST EMBED
-- typeSort tce (TyConApp c [])
--   | k == intTyConKey     = FInt
--   | k == intPrimTyConKey = FInt
--   | k == integerTyConKey = FInt 
--   | k == boolTyConKey    = FBool
--   where k = tyConUnique c
typeSort tce (ForAllTy _ τ) 
  = typeSort tce τ  -- JHALA: Yikes! Fix!!!
typeSort tce (FunTy τ1 τ2) 
  = typeSortFun tce τ1 τ2
typeSort tce (TyConApp c τs)
  = fApp ftc (typeSort tce <$> τs)
  where ftc = fromMaybe (stringFTycon $ tyConName c) (M.lookup c tce) 
typeSort _ τ
  = FObj $ typeUniqueSymbol τ
  
tyConName c 
  | listTyCon == c = listConName
  | isTupleTyCon c = tupConName
  | otherwise      = showPpr c


typeSortFun tce τ1 τ2
  = FFunc n $ genArgSorts sos
  where sos  = typeSort tce <$> τs
        τs   = τ1  : grabArgs [] τ2
        n    = (length sos) - 1
   


typeUniqueSymbol :: Type -> Symbol 
typeUniqueSymbol = stringSymbol . {- ("sort_" ++) . -} showSDocDump . ppr

grabArgs τs (FunTy τ1 τ2 ) = grabArgs (τ1:τs) τ2
grabArgs τs τ              = reverse (τ:τs)

genArgSorts' sos = traceShow ("genArgSorts sos = " ++ showPpr sos) $ genArgSorts sos

genArgSorts :: [Sort] -> [Sort]
--genArgSorts xs = zipWith genIdx xs $ memoIndex genSort xs
--  where genSort FInt        = Nothing
--        genSort FBool       = Nothing 
--        genSort so          = Just so
--        genIdx  _ (Just i)  = FVar i
--        genIdx  so  _       = so

genArgSorts xs = sortSubst su <$> xs
  where su = M.fromList $ zip (sortNub αs) (FVar <$> [0..])
        αs = concatMap getObjs xs 

getObjs (FObj x)          = [x]
getObjs (FFunc _ ts)      = concatMap getObjs ts
getObjs (FApp _ ts)       = concatMap getObjs ts
getObjs _                 = []

sortSubst su t@(FObj x)   = fromMaybe t (M.lookup x su) 
sortSubst su (FFunc n ts) = FFunc n (sortSubst su <$> ts)
sortSubst su (FApp c ts)  = FApp c  (sortSubst su <$> ts)
sortSubst _  t            = t

newtype Sub = Sub [(Int, Sort)]

instance Fixpoint Sort where
  toFix = toFix_sort

toFix_sort (FVar i)     = text "@"   <> parens (ppr i)
toFix_sort FInt         = text "int"
toFix_sort FBool        = text "bool"
toFix_sort (FObj x)     = toFix x
toFix_sort FNum         = text "num"
toFix_sort (FFunc n ts) = text "func" <> parens ((ppr n) <> (text ", ") <> (toFix ts))
toFix_sort (FApp c [t]) 
  | isListTC c          = brackets $ toFix_sort t 
toFix_sort (FApp c ts)  = toFix c <+> intersperse space (fp <$> ts)
                          where fp s@(FApp _ (_:_)) = parens $ toFix_sort s 
                                fp s                = toFix_sort s


instance Fixpoint FTycon where
  toFix (TC s)       = toFix s

---------------------------------------------------------------
---------------------------- Symbols --------------------------
---------------------------------------------------------------

symChars 
  =  ['a' .. 'z']
  ++ ['A' .. 'Z'] 
  ++ ['0' .. '9'] 
  ++ ['_', '%', '.', '#']

data Symbol = S !String 
              deriving (Eq, Ord, Data, Typeable)

instance Fixpoint Symbol where
  toFix (S x) = text x

instance Outputable Symbol where
  ppr (S x) = text x 

instance Outputable Sort where
  ppr = text . show 

instance Show Symbol where
  show (S x) = x

newtype Subst  = Su (M.Map Symbol Expr) 
                 deriving (Eq, Ord, Data, Typeable)

instance Outputable Refa where
  ppr  = text . show

instance Outputable Expr where
  ppr  = text . show

instance Outputable Subst where
  ppr (Su m) = ppr (M.toList m)

instance Show Subst where
  show = showPpr

instance Fixpoint Subst where
  toFix (Su m) = case M.toAscList m of 
                   []  -> empty
                   xys -> hcat $ map (\(x,y) -> brackets $ (toFix x) <> text ":=" <> (toFix y)) xys


---------------------------------------------------------------------------
------ Converting Strings To Fixpoint ------------------------------------- 
---------------------------------------------------------------------------

stringFTycon :: String -> FTycon
stringFTycon = TC . stringSymbol . dropModuleNames

stringSymbolRaw :: String -> Symbol
stringSymbolRaw = S

stringSymbol :: String -> Symbol
stringSymbol s
  | isFixSym' s = S s 
  | otherwise   = S $ fixSymPrefix ++ concatMap encodeChar s

symbolString :: Symbol -> String
symbolString (S str) 
  = case chopPrefix fixSymPrefix str of
      Just s  -> concat $ zipWith tx indices $ chunks s 
      Nothing -> str
    where chunks = unIntersperse symSep 
          tx i s = if even i then s else [decodeStr s]

indices :: [Integer]
indices = [0..]

okSymChars
  =  ['a' .. 'z']
  ++ ['A' .. 'Z'] 
  ++ ['0' .. '9'] 
  ++ ['_', '.'  ]

symSep = '#'
fixSymPrefix = "fix" ++ [symSep]


isFixSym' (c:chs) = isAlpha c && all (`elem` (symSep:okSymChars)) chs
isFixSym' _       = False

encodeChar c 
  | c `elem` okSymChars 
  = [c]
  | otherwise
  = [symSep] ++ (show $ ord c) ++ [symSep]

decodeStr s 
  = chr ((read s) :: Int)

qualifySymbol x sy 
  | isQualified x' = sy 
  | isParened x'   = stringSymbol (wrapParens (x ++ "." ++ stripParens x')) 
  | otherwise      = stringSymbol (x ++ "." ++ x')
  where x' = symbolString sy 

isQualified y         = '.' `elem` y 
wrapParens x          = "(" ++ x ++ ")"
isParened xs          = xs /= stripParens xs

---------------------------------------------------------------------

vv                      = S vvName 
dummySymbol             = S dummyName
-- tagSymbol               = S tagName
intSymbol x i           = S $ x ++ show i           

tempSymbol              ::  String -> Integer -> Symbol
tempSymbol prefix n     = intSymbol (tempPrefix ++ prefix) n

-- isTempSym (S x)         = tempPrefix `isPrefixOf` x
tempPrefix              = "lq_tmp_"
anfPrefix               = "lq_anf_" 
nonSymbol               = S ""
isNonSymbol             = (0 ==) . length . symbolString

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

instance Fixpoint Pred where
  toFix PTop             = text "???"
  toFix PTrue            = text "true"
  toFix PFalse           = text "false"
  toFix (PBexp e)        = parens $ text "?" <+> toFix e
  toFix (PNot p)         = parens $ text "~" <+> parens (toFix p)
  toFix (PImp p1 p2)     = parens $ (toFix p1) <+> text "=>" <+> (toFix p2)
  toFix (PIff p1 p2)     = parens $ (toFix p1) <+> text "<=>" <+> (toFix p2)
  toFix (PAnd ps)        = text "&&" <+> toFix ps
  toFix (POr  ps)        = text "||" <+> toFix ps
  toFix (PAtom r e1 e2)  = parens $ toFix e1 <+> toFix r <+> toFix e2
  toFix (PAll xts p)     = text "forall" <+> (toFix xts) <+> text "." <+> (toFix p)

  simplify (PAnd [])     = PTrue
  simplify (POr  [])     = PFalse
  simplify (PAnd [p])    = simplify p
  simplify (POr  [p])    = simplify p
  simplify (PAnd ps)    
    | any isContra ps    = PFalse
    | otherwise          = PAnd $ map simplify ps
  simplify (POr  ps)    
    | any isTautoPred ps = PTrue
    | otherwise          = POr  $ map simplify ps 
  simplify p            
    | isContra p         = PFalse
    | isTautoPred  p     = PTrue
    | otherwise          = p

zero         = ECon (I 0)
one          = ECon (I 1)
isContra     = (`elem` [ PAtom Eq zero one, PAtom Eq one zero, PFalse])   
isTautoPred  = (`elem` [ PTrue ])

isTautoReft (Reft (_, ras)) = all isTautoRa ras
isTautoRa (RConc p)         = isTautoPred p
isTautoRa _                 = False

isSingletonReft (Reft (v, [RConc (PAtom Eq e1 e2)])) 
  | e1 == EVar v = Just e2
  | e2 == EVar v = Just e1
isSingletonReft _    = Nothing 

pAnd          = simplify . PAnd 
pOr           = simplify . POr 
pIte p1 p2 p3 = pAnd [p1 `PImp` p2, (PNot p1) `PImp` p3] 

ppr_reft (Reft (v, ras)) d 
  | all isTautoRa ras
  = d
  | otherwise
  = braces (ppr v <+> colon <+> d <+> text "|" <+> ppRas ras)

ppr_reft_pred (Reft (_, ras))
  | all isTautoRa ras
  = text "true"
  | otherwise
  = ppRas ras

ppRas = cat . punctuate comma . map toFix . flattenRefas

---------------------------------------------------------------
----------------- Refinements ---------------------------------
---------------------------------------------------------------

data Refa 
  = RConc !Pred 
  | RKvar !Symbol !Subst
  deriving (Eq, Ord, Data, Typeable, Show)

data Reft
  = Reft (Symbol, [Refa]) 
  deriving (Eq, Ord, Data, Typeable) 

instance Show Reft where
  show (Reft x) = showSDoc $ toFix x 

instance Outputable Reft where
  ppr = ppr_reft_pred

data SortedReft
  = RR { sr_sort :: !Sort, sr_reft :: !Reft }
  deriving (Eq, Ord, Data, Typeable) 

isNonTrivialSortedReft (RR _ (Reft (_, ras)))
  = not $ null ras

isFunctionSortedReft (RR (FFunc _ _) _)
  = True
isFunctionSortedReft _
  = False

---------------------------------------------------------------
----------------- Environments  -------------------------------
---------------------------------------------------------------

newtype SEnv a = SE (M.Map Symbol a) 
                 deriving (Eq, Ord, Data, Typeable) 

fromListSEnv            = SE . M.fromList
deleteSEnv x (SE env)   = SE (M.delete x env)
insertSEnv x y (SE env) = SE (M.insert x y env)
lookupSEnv x (SE env)   = M.lookup x env
emptySEnv               = SE M.empty
memberSEnv x (SE env)   = M.member x env
-- domainSEnv (SE env)     = M.keys env

instance Functor SEnv where
  fmap f (SE m) = SE $ fmap f m

type FEnv = SEnv SortedReft 

-- instance Fixpoint (PVar Type) where
--   toFix (PV s _ a) 
--    = parens $ toFix s <+> sep (toFix . thd3 <$> a)

instance Fixpoint Refa where
  toFix (RConc p)    = toFix p
  toFix (RKvar k su) = toFix k <> toFix su
  -- toFix (RPvar p)    = toFix p

instance Fixpoint SortedReft where
  toFix (RR so (Reft (v, ras))) 
    = braces 
    $ (toFix v) <+> (text ":") <+> (toFix so) <+> (text "|") <+> toFix ras

instance Outputable SortedReft where
  ppr = toFix

instance Fixpoint FEnv where
  toFix (SE m)  = toFix (M.toAscList m)

insertFEnv   = insertSEnv . lower 
  where lower x@(S (c:chs)) 
          | isUpper c = S $ toLower c : chs
          | otherwise = x
        lower z       = z

instance (Outputable a) => Outputable (SEnv a) where
  ppr (SE e) = vcat $ map pprxt $ M.toAscList e
	where pprxt (x, t) = ppr x <+> dcolon <+> ppr t

instance Outputable (SEnv a) => Show (SEnv a) where
  show = showSDoc . ppr

-----------------------------------------------------------------------------------
------------------------- Constraints ---------------------------------------------
-----------------------------------------------------------------------------------

data SubC a = SubC { senv  :: !FEnv
                   , sgrd  :: !Pred
                   , slhs  :: !SortedReft
                   , srhs  :: !SortedReft
                   , sid   :: !(Maybe Integer)
                   , stag  :: ![Int] 
                   , sinfo :: !a
                   } deriving (Eq, Ord, Data, Typeable)

data WfC a  = WfC  { wenv  :: !FEnv
                   , wrft  :: !SortedReft
                   , wid   :: !(Maybe Integer) 
                   , winfo :: !a
                   } deriving (Eq, Ord, Data, Typeable)

data FixResult a = Crash [a] String | Safe | Unsafe ![a] | UnknownError

type FixSolution = M.Map Symbol Pred

instance Monoid (FixResult a) where
  mempty                          = Safe
  mappend Safe x                  = x
  mappend x Safe                  = x
  mappend _ c@(Crash _ _)         = c 
  mappend c@(Crash _ _) _         = c 
  mappend (Unsafe xs) (Unsafe ys) = Unsafe (xs ++ ys)
  mappend UnknownError _          = UnknownError
  mappend _ UnknownError          = UnknownError

instance Functor FixResult where 
  fmap f (Crash xs msg) = Crash (f <$> xs) msg
  fmap f (Unsafe xs)    = Unsafe (f <$> xs)
  fmap _ Safe           = Safe
  fmap _ UnknownError   = UnknownError 

instance (Ord a, Outputable a) => Outputable (FixResult (SubC a)) where
  ppr (Crash xs msg) = text "Crash!\n"  <> ppr_sinfos "CRASH: " xs <> parens (text msg) 
  ppr Safe           = text "Safe"
  ppr (Unsafe xs)    = text "Unsafe:\n" <> ppr_sinfos "WARNING: " xs
  ppr UnknownError   = text "Unknown Error!"

ppr_sinfos :: (Ord a, Outputable a) => String -> [SubC a] -> SDoc
ppr_sinfos msg = (text msg  <>) . ppr . sort . fmap sinfo

-- toFixPfx s x     = text s <+> toFix x

instance Show (SubC a) where
  show = showPpr 

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

instance Subable Symbol where
  subst (Su s) x           = subSymbol (M.lookup x s) x

subSymbol (Just (EVar y)) _ = y
subSymbol Nothing         x = x
subSymbol _               _ = error "sub Symbol"

instance Subable Expr where
  subst su (EApp f es)     = EApp f $ map (subst su) es 
  subst su (EBin op e1 e2) = EBin op (subst su e1) (subst su e2)
  subst su (EIte p e1 e2)  = EIte (subst su p) (subst su e1) (subst  su e2)
  subst su (ECst e so)     = ECst (subst su e) so
  subst (Su s) e@(EVar x)  = M.findWithDefault e x s
  subst _ e                = e

instance Subable Pred where
  subst su (PAnd ps)       = PAnd $ map (subst su) ps
  subst su (POr  ps)       = POr  $ map (subst su) ps
  subst su (PNot p)        = PNot $ subst su p
  subst su (PImp p1 p2)    = PImp (subst su p1) (subst su p2)
  subst su (PIff p1 p2)    = PIff (subst su p1) (subst su p2)
  subst su (PBexp e)       = PBexp $ subst su e
  subst su (PAtom r e1 e2) = PAtom r (subst su e1) (subst su e2)
  subst _  (PAll _ _)      = errorstar $ "subst: FORALL" 
  subst _  p               = p

instance Subable Refa where
  subst su (RConc p)     = RConc   $ subst su p
  subst su (RKvar k su') = RKvar k $ su' `catSubst` su 
  -- subst _  (RPvar p)     = RPvar p

instance (Subable a, Subable b) => Subable (a,b) where
  subst su (x,y) = (subst su x, subst su y)

instance Subable a => Subable [a] where
  subst su = map $ subst su

instance Subable a => Subable (M.Map k a) where
  subst su = M.map $ subst su

instance Subable Reft where
  subst su (Reft (v, ras)) = Reft (v, subst su ras)

instance Monoid Reft where
  mempty  = trueReft
  mappend (Reft (v, ras)) (Reft (v', ras')) 
    | v == v'   = Reft (v, ras ++ ras')
    | otherwise = Reft (v, ras ++ (ras' `subst1` (v', EVar v)))

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

exprReft e    = Reft (vv, [RConc $ PAtom Eq (EVar vv) e])
notExprReft e = Reft (vv, [RConc $ PAtom Ne (EVar vv) e])

trueSortedReft :: Sort -> SortedReft
trueSortedReft = (`RR` trueReft) 

trueReft = Reft (vv, [])

trueRefa = RConc PTrue

canonReft r@(Reft (v, ras)) 
  | v == vv    = r 
  | otherwise = Reft (vv, ras `subst1` (v, EVar vv))

flattenRefas ::  [Refa] -> [Refa]
flattenRefas = concatMap flatRa
  where flatRa (RConc p) = RConc <$> flatP p
        flatRa ra        = [ra]
        flatP  (PAnd ps) = concatMap flatP ps
        flatP  p         = [p]

----------------------------------------------------------------
---------------------- Strictness ------------------------------
----------------------------------------------------------------

instance NFData Symbol where
  rnf (S x) = rnf x

instance NFData FTycon where
  rnf (TC c)       = rnf c

instance NFData Sort where
  rnf (FVar x)     = rnf x
  rnf (FFunc n ts) = rnf n `seq` (rnf <$> ts) `seq` () 
  rnf (FApp c ts)  = rnf c `seq` (rnf <$> ts) `seq` ()
  rnf (z)          = z `seq` ()

instance NFData Sub where
  rnf (Sub x) = rnf x

instance NFData Subst where
  rnf (Su x) = rnf x

instance NFData FEnv where
  rnf (SE x) = rnf x

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
  -- rnf (RPvar _)     = () -- rnf x

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

class MapSymbol a where
  mapSymbol :: (Symbol -> Symbol) -> a -> a

instance MapSymbol Refa where
  mapSymbol f (RConc p)    = RConc (mapSymbol f p)
  mapSymbol f (RKvar s su) = RKvar (f s) su
  -- mapSymbol _ (RPvar p)    = RPvar p -- RPvar (mapSymbol f p)

instance MapSymbol Reft where
  mapSymbol f (Reft(s, rs)) = Reft(f s, map (mapSymbol f) rs)

instance MapSymbol Pred where
  mapSymbol f (PAnd ps)       = PAnd (mapSymbol f <$> ps)
  mapSymbol f (POr ps)        = POr (mapSymbol f <$> ps)
  mapSymbol f (PNot p)        = PNot (mapSymbol f p)
  mapSymbol f (PImp p1 p2)    = PImp (mapSymbol f p1) (mapSymbol f p2)
  mapSymbol f (PIff p1 p2)    = PIff (mapSymbol f p1) (mapSymbol f p2)
  mapSymbol f (PBexp e)       = PBexp (mapSymbol f e)
  mapSymbol f (PAtom b e1 e2) = PAtom b (mapSymbol f e1) (mapSymbol f e2)
  mapSymbol _ (PAll _ _)      = error "mapSymbol PAll"
  mapSymbol _ p               = p 

instance MapSymbol Expr where
  mapSymbol f (EVar s)       = EVar $ f s
  mapSymbol f (EDat s so)    = EDat (f s) so
  mapSymbol f (ELit s so)    = ELit (f s) so
  mapSymbol f (EApp s es)    = EApp (f s) (mapSymbol f <$> es)
  mapSymbol f (EBin b e1 e2) = EBin b (mapSymbol f e1) (mapSymbol f e2)
  mapSymbol f (EIte p e1 e2) = EIte (mapSymbol f p) (mapSymbol f e1) (mapSymbol f e2)
  mapSymbol f (ECst e s)     = ECst (mapSymbol f e) s 
  mapSymbol _ e              = e

