{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Language.Haskell.Liquid.Bare.Axiom (makeHaskellAxioms) where

import Prelude hiding (error)
import CoreSyn
import TyCon
import DataCon
import Id
import Name
import Type hiding (isFunTy)
import Var
import TypeRep

import Prelude hiding (mapM)

import           Control.Monad hiding (forM, mapM)
import           Control.Monad.Except hiding (forM, mapM)
import           Control.Monad.State hiding (forM, mapM)

import           Text.PrettyPrint.HughesPJ (text)
import qualified Data.List    as L
import qualified Data.HashSet as S
import           Language.Fixpoint.Misc
import           Language.Fixpoint.Types (Symbol, symbol, symbolString)

import qualified Language.Haskell.Liquid.Measure as Ms
import qualified Language.Fixpoint.Types as F
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Transforms.CoreToLogic
import           Language.Haskell.Liquid.GHC.Misc
import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Bare.Env


--------------------------------------------------------------------------------
makeHaskellAxioms
  :: F.TCEmb TyCon -> [CoreBind] -> Ms.BareSpec -> BareM [ (LocSymbol, LocSpecType)]
--------------------------------------------------------------------------------
makeHaskellAxioms tce cbs sp = do
  let xs       = S.toList $ Ms.reflects sp
  lmap        <- logicEnv <$> get
  (_,xts,_,_) <- L.unzip4 <$> mapM (makeAxiom tce lmap cbs) xs
  return [ (namedLocSymbol x, t) | (x, t) <- concat xts ]

--------------------------------------------------------------------------------
makeAxiom :: F.TCEmb TyCon
          -> LogicMap
          -> [CoreBind]
          -> LocSymbol
          -> BareM ( (Symbol, LocSpecType) -- ^ reflected symbol, sort
                   , [(Var, LocSpecType)]  -- ^ [ONLY OUTPUT THAT MATTERS] reflected vars and reflected-refinement types
                   , [Var]                 -- ^ reflected vars
                   , F.Expr                -- ^ quantified formula?
                   )
--------------------------------------------------------------------------------
makeAxiom tce lmap cbs x
  = case findVarDef (val x) cbs of
      Just (v, def) -> makeAxiom' tce lmap cbs x v def
      Nothing       -> throwError $ mkError x "Cannot lift haskell function"

  -- REFLECT-IMPORTS = case filter ((val x `elem`) . map (dropModuleNames . simplesymbol) . binders) cbs of
        -- REFLECT-IMPORTS (NonRec v def:_)   ->
        -- REFLECT-IMPORTS (Rec [(v, def)]:_) -> makeAxiom' tce lmap cbs spec x v def
        -- REFLECT-IMPORTS [Rec xes]          -> throwError $ mkError x
                                -- REFLECT-IMPORTS ("Cannot extract measure from mutually recursive haskell functions" ++ (show (fst <$> xes)))
        -- REFLECT-IMPORTS _                  -> throwError $ mkError x "Cannot extract measure from haskell function"

--------------------------------------------------------------------------------
makeAxiom' :: F.TCEmb TyCon
           -> LogicMap
           -> [CoreBind]
           -> LocSymbol
           -> Var
           -> CoreExpr
           -> BareM ((Symbol, LocSpecType), [(Var, LocSpecType)], [Var], F.Expr)
--------------------------------------------------------------------------------
makeAxiom' tce lmap cbs x v def = do
  let anames = findAxiomNames x cbs
  let haxs   = defAxioms anames v def
  vts <- zipWithM (makeAxiomType tce lmap x) (reverse anames) haxs
  insertAxiom v (val x)
  updateLMap lmap x x v
  updateLMap lmap (x{val = (symbol . showPpr . getName) v}) x v
  let (t, e) = makeAssumeType tce lmap x v anames  def
  return ( F.tracepp "makeAxiom 1" $ (val x, mkType x v)
         , F.tracepp "makeAxiom 2" $ (v, t) : vts     -- ASKNIKI: What is vts for?
         , fst . aname <$> haxs                       -- ASKNIKI: dead?
         , F.tracepp "makeAxiom 3" $ e )              -- ASKNIKI: What is this for?

mkError :: LocSymbol -> String -> Error
mkError x str = ErrHMeas (sourcePosSrcSpan $ loc x) (pprint $ val x) (text str)

mkType :: LocSymbol -> Var -> Located SpecType
mkType x v = x {val = ufType $ varType v}

-- ASKNIKI: what is this function doing?!

makeAssumeType :: F.TCEmb TyCon -> LogicMap -> LocSymbol ->  Var ->  [a] -> CoreExpr
               -> (LocSpecType, F.Expr)
makeAssumeType tce lmap x v ams def = assumedtype
  where
    assumedtype
      | not (null ams)
      = (x {val = at}, F.PTrue)
      | isBool (ty_res trep)
      = (x {val = at `strengthenRes` F.subst su bref}, makeSMTAxiomBool xss ble)
      | otherwise
      = (x {val = at `strengthenRes` F.subst su ref},  makeSMTAxiom     xss le )

    makeSMTAxiomBool xss ble = F.PAll xss (F.PAtom F.Eq (F.mkEApp x (F.EVar . fst <$> xss)) ble)
    makeSMTAxiom     xss  le = F.PAll xss (F.PIff (F.mkProp (F.mkEApp x (F.EVar . fst <$> xss))) le)

    trep = toRTypeRep t
    t    = ofType $ varType v
    at   = axiomType x t

    le = case runToLogicWithBoolBinds bbs tce lmap mkErr (coreToLogic def') of
           Right e -> e
           Left  e -> panic Nothing $ show e

    ble = case runToLogicWithBoolBinds bbs tce lmap mkErr (coreToPred def') of
           Right e -> e
           Left  e -> panic Nothing $ show e
    ref  = F.Reft (F.vv_, F.PAtom F.Eq (F.EVar F.vv_) le)
    bref = F.Reft (F.vv_, F.PIff (F.mkProp $ F.EVar F.vv_) ble)

    mkErr s = ErrHMeas (sourcePosSrcSpan $ loc x) (pprint $ val x) (text s)

    bbs     = filter isBoolBind xs

    (xs, def') = grapBody $ normalize def
    su = F.mkSubst $
                zip (F.symbol <$> xs) (F.EVar <$> ty_non_dict_binds (toRTypeRep at))
             ++ zip (simplesymbol <$> xs) (F.EVar <$> ty_non_dict_binds (toRTypeRep at))


    grapBody (Lam x e)  = let (xs, e') = grapBody e in (x:xs, e')
    grapBody (Tick _ e) = grapBody e
    grapBody e          = ([], e)

    xss = [(mkSymbol x t, rTypeSort tce t) | (x, t) <- zip xs (ty_args (toRTypeRep at)), not (isClassType t)]

    mkSymbol x t = if isFunTy t then simplesymbol x else F.symbol x


    ty_non_dict_binds trep = [x | (x, t) <- zip (ty_binds trep) (ty_args trep), not (isClassType t)]


isBoolBind :: Var -> Bool
isBoolBind v = isBool (ty_res $ toRTypeRep ((ofType $ varType v) :: RRType ()))


strengthenRes :: SpecType -> F.Reft -> SpecType
strengthenRes t r = fromRTypeRep $ trep {ty_res = ty_res trep `strengthen` F.ofReft r }
  where
    trep = toRTypeRep t

updateLMap :: LogicMap -> LocSymbol -> LocSymbol -> Var -> BareM ()
updateLMap _ _ _ v | not (isFun $ varType v)
  = return ()
  where
    isFun (FunTy _ _)    = True
    isFun (ForAllTy _ t) = isFun t
    isFun  _             = False

updateLMap _ x y vv
  = insertLogicEnv "UPDATELMAP" x ys (F.eApps (F.EVar $ val y) (F.EVar <$> ys))
  where
    nargs = dropWhile isClassType $ ty_args trep
    trep  = toRTypeRep ((ofType $ varType vv) :: RRType ())
    ys    = zipWith (\i _ -> symbol (("x" ++ show i) :: String)) [1..] nargs

makeAxiomType :: F.TCEmb TyCon -> LogicMap -> LocSymbol -> Var -> HAxiom -> BareM (Var, Located SpecType)
makeAxiomType tce lmap x v (Axiom _ _ xs _ lhs rhs)
  = do foldM_ (\lm x -> (updateLMap lm (dl x) (dl x) x >> (logicEnv <$> get))) lmap xs
       return (v, x{val = t})
  where
    dl   = dummyLoc . F.symbol
    t    = fromRTypeRep $  tr{ty_res = res, ty_binds = symbol <$> xs}
    tt   = ofType $ varType v
    tr   = toRTypeRep tt
    res  = ty_res tr `strengthen` MkUReft ref mempty mempty
    llhs = toLogic tce lmap x lhs
    lrhs = toLogic tce lmap x rhs
    ref  = F.Reft (F.vv_, F.PAtom F.Eq llhs lrhs)

toLogic :: F.TCEmb TyCon -> LogicMap -> LocSymbol -> CoreExpr -> F.Expr
toLogic tce lmap x thing
  = case runToLogic tce lmap (mkErr x) (coreToLogic thing) of
      Right e -> e
      Left e  -> panic Nothing $ show e

mkErr :: LocSymbol -> String -> TError t
mkErr x s = ErrHMeas (sourcePosSrcSpan $ loc x) (pprint $ val x) (text s)

-- ASKNIKI: what is this for? can we delete it?
findAxiomNames :: Located Symbol -> [Bind CoreBndr] -> [CoreBndr]
findAxiomNames x (NonRec v _ :cbs) | isAxiomName x v = v:findAxiomNames x cbs
findAxiomNames x (Rec [(v,_)]:cbs) | isAxiomName x v = v:findAxiomNames x cbs
findAxiomNames x (_:cbs)                             = findAxiomNames x cbs
findAxiomNames _ []                                  = []

isAxiomName :: Located Symbol -> CoreBndr -> Bool
isAxiomName x v =
  (("axiom_" ++ symbolString (val x)) `L.isPrefixOf`) (symbolString $ dropModuleNames $ simplesymbol v)

defAxioms :: [Var] -> Var -> CoreExpr -> [Axiom Var Kind (Expr Var)]
defAxioms vs v e = go [] $ normalize e
  where
     go bs (Tick _ e) = go bs e
     go bs (Lam x e) | isTyVar x               = go bs e
     go bs (Lam x e) | isClassPred (varType x) = go bs e
     go bs (Lam x e) = go (bs++[x]) e
     go bs (Case  (Var x) _ _ alts)  = goalt x bs  <$> alts
     go bs e         = [Axiom (v, Nothing) (getSimpleName v) bs (varType <$> bs) (foldl App (Var v) (Var <$> bs)) e]

     goalt x bs (DataAlt c, ys, e) = let vs = [b | b<- bs , b /= x] ++ ys in
        Axiom (v, Just c) (getConName v c)  vs (varType <$> vs) (mkApp bs x c ys) $ normalize e
     goalt _ _  (LitAlt _,  _,  _) = todo Nothing "defAxioms: goalt Lit"
     goalt _ _  (DEFAULT,   _,  _) = todo Nothing "defAxioms: goalt Def"

     mkApp bs x c ys = foldl App (Var v) ((\y -> if y == x then mkConApp c (Var <$> ys) else Var y) <$> bs)

     getSimpleName v = filterSingle (isSimple v) vs
     getConName v c  = filterSingle (isCon v c) vs

     isSimple v n    = simpleString n == axiomString v
     simpleString    = symbolString . dropModuleNames . simplesymbol
     axiomString     = ("axiom_" ++) . simpleString
     isCon v c n     = simpleString n == axiomString v ++ "_" ++ simpleString (dataConWorkId c)

filterSingle :: (a -> Bool) -> [a] -> Maybe a
filterSingle  f xs = case filter f xs of
                      [x] -> Just x
                      _   -> Nothing
{-

unANF :: Bind Var -> Expr Var -> Expr Var
unANF (NonRec x ex) e | L.isPrefixOf "lq_anf" (show x)
  = subst (x, ex) e
unANF b e = Let b e
-}

class Subable a where
  subst :: (Var, CoreExpr) -> a -> a

instance Subable Var where
  subst (x, ex) z | x == z, Var y <- ex = y
                  | otherwise           = z

instance Subable CoreExpr where
  subst (x, ex) (Var y)
    | x == y    = ex
    | otherwise = Var y
  subst su (App f e)
    = App (subst su f) (subst su e)
  subst su (Lam x e)
    = Lam x (subst su e)
  subst su (Case e x t alts)
    = Case (subst su e) x t (subst su <$> alts)
  subst su (Let (Rec xes) e)
    = Let (Rec (mapSnd (subst su) <$> xes)) (subst su e)
  subst su (Let (NonRec x ex) e)
    = Let (NonRec x (subst su ex)) (subst su e)
  subst su (Cast e t)
    = Cast (subst su e) t
  subst su (Tick t e)
    = Tick t (subst su e)
  subst _ (Lit l)
    = Lit l
  subst _ (Coercion c)
    = Coercion c
  subst _ (Type t)
    = Type t

instance Subable CoreAlt where
  subst su (c, xs, e) = (c, xs, subst su e)

-- | Specification for Haskell function
axiomType :: LocSymbol -> SpecType -> SpecType
axiomType s t' = fromRTypeRep $ t{ty_res = res, ty_binds = xs'}
  where
    t   = toRTypeRep t'
    xs  = fst $ unzip (dropWhile (isClassType . snd) $ zip xs' (ty_args t))
    xs' = if isUnique (ty_binds t)
            then ty_binds t
             else (\i -> symbol ("xa" ++ show i)) <$> [1..(length $ ty_binds t)]
    x  = F.vv_

    res = ty_res t `strengthen` MkUReft ref mempty mempty

    ref = if isBool (ty_res t) then bref else eref

    eref  = F.Reft (x, F.PAtom F.Eq (F.EVar x) (mkApp xs))
    bref  = F.Reft (x, F.PIff (F.mkProp (F.EVar x)) (mkApp xs))

    mkApp = F.mkEApp s . map F.EVar

    isUnique xs = length xs == length (L.nub xs)


-- | Type for uninterpreted function that approximated Haskell function into logic
ufType :: (F.Reftable r) => Type -> RRType r
ufType τ = fromRTypeRep $ t{ty_args = args, ty_binds = xs, ty_refts = rs}
  where
    t          = toRTypeRep $ ofType τ
    (args, xs, rs) = unzip3 $ dropWhile (isClassType . fst3) $ zip3 (ty_args t) (ty_binds t) (ty_refts t)
