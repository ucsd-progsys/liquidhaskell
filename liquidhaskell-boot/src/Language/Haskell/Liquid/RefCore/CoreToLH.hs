{-# LANGUAGE ConstraintKinds #-}
{-# OPTIONS_GHC -Wall #-}

-- |
-- - Main module for the translation between GHC Core Haskell and RefCore Calculus
module Language.Haskell.Liquid.RefCore.CoreToLH (transBind, Def (..)) where

import Control.Exception (assert)
import Data.Bifunctor (first, second)
-- import           Data.Char (isUpper)

-- import GHC.Parser.Annotation
-- import GHC.Types.Var hiding (Id)
-- import GHC.Types.SrcLoc

import Data.Char (isDigit)
import Data.Data (Data, showConstr, toConstr)
import qualified Data.HashMap.Strict as HM
import Data.List (find, intercalate, isPrefixOf)
import qualified Data.Map.Strict as M
import Data.Maybe (mapMaybe)
import qualified Data.Set as S
import qualified Data.Text as Text
import Text.PrettyPrint.HughesPJClass hiding (first)

import Debug.Trace (trace)
import GHC.Core
import GHC.Core.TyCo.Rep
import GHC.Types.Literal
import GHC.Types.Name (NamedThing, getSrcSpan)
import GHC.Utils.Outputable (ppr, showSDocUnsafe)
import           Language.Haskell.Liquid.GHC.Misc (isDataConId)
import           Language.Haskell.Liquid.Types.RType (SpecType)
import           Language.Haskell.Liquid.Types.Types (AnnInfo (..))
import qualified Language.Haskell.Liquid.Types.Types ()

import qualified Language.Haskell.Liquid.RefCore.SpecToLH as SLH
import           Language.Haskell.Liquid.RefCore.Misc
import           Language.Haskell.Liquid.RefCore.Names (Id, hashName)
import qualified Language.Haskell.Liquid.RefCore.Calculus as Calc

-- | Constraint synonym for GHC Core binder variables
type CoreBinder b = (Data b, Show b, NamedThing b)

-- | A top-level definition extracted from GHC Core
data Def = Def
  { -- | the name of the definition
    defName :: Id,
    -- | the argument names
    defArgs :: [Id],
    -- | the translated body
    defBody :: Calc.Expr,
    -- | whether the definition is recursive
    defIsRec :: Bool
  }
  deriving (Eq, Show)

-- TODO move these to Calculus

-- | A case branch in Calculus format
-- TODO convert to Data type with named fields for better readability
type Branch = ((Id, [(Id, Bool)]), Maybe Calc.Expr)

brCon :: Branch -> Id
brCon = fst . fst

brVarsWithInd :: Branch -> [(Id, Bool)]
brVarsWithInd = snd . fst

brVars :: Branch -> [Id]
brVars = map fst . brVarsWithInd

brBody :: Branch -> Maybe Calc.Expr
brBody = snd

modifyBrBody :: (Calc.Expr -> Calc.Expr) -> Branch -> Branch
modifyBrBody f ((c, xs), Just body) = ((c, xs), Just (f body))
modifyBrBody _ br = br

-- | Check if a variable occurs free in an expression
occursFreeIn :: Id -> Calc.Expr -> Bool
occursFreeIn x e = x `S.member` Calc.freeVars e

-- | Represent undefined/unreachable as a marker expression
undefinedReft :: Calc.Reft
undefinedReft = Calc.mkVar "undefined"

-- | Translate Haskell binders, with mutually recursive binders unsupported for now.
-- Entry point for the translations in this module
--
-- > transBind(NonRec f = e) = trans(f,e)
-- > transBind(Rec [f_1 = e_1, …, f_n = e_n]) = trans(f_1,e_1)
transBind :: (CoreBinder b) => String -> AnnInfo SpecType -> Bind b -> Def
transBind modId infTypes binds = case binds of
  NonRec b e -> mkDef b e
  Rec [(b, e)] -> mkDef b e
  Rec defs -> error $ "Mutually recursive definitions " ++ show (map fst defs) ++ " not yet supported."
  where
    mkDef b e =
      let (args, body) = flattenFun modId infTypes (f b) e
       in Def (f b) args body False
    f b = stripLegalName modId $ show b

-- | Classification of application head symbols.
data HeadSymbol
  = HNot
  | HLambda
  | HEqChain Calc.ProofOp
  | HCast
  | HQmark
  | HPatError
  | HConst Calc.Reft
  | HUnbox
  | HBinOp Calc.Bop
  | HGeneric Id
  | HDC Id
  deriving (Show)

-- | Classify an application head name into a 'HeadSymbol'.
classifyHead :: Id -> HeadSymbol
classifyHead "not" = HNot
classifyHead "lambda" = HLambda
classifyHead "===" = HEqChain Calc.PEq
classifyHead "=<=" = HEqChain Calc.PLeq
classifyHead "=>=" = HEqChain Calc.PGeq
classifyHead "***" = HCast
classifyHead "?" = HQmark
classifyHead "patError" = HPatError
classifyHead n
  | M.member n SLH.builtinDCs = HConst (transName n)
  | n `elem` ["I#", "I"] = HUnbox
  | Just op <- M.lookup n SLH.bops = HBinOp op
  | otherwise = HGeneric n

-- | The head of a flattened Core application.
data AppHead
  = -- | a classified variable
    VarHead HeadSymbol
  | -- | a non-variable expression
    ReftHead Calc.Reft

instance Pretty AppHead where
  pPrint (VarHead sym) = text "VarHead" <+> text (show sym)
  pPrint (ReftHead r) = text "ReftHead" <+> pPrint r

-- | Flatten and translate an application, returning a structured head and
-- surrounding let-bindings used to extract expressions from refinements
flattenCoreApp :: (CoreBinder b) => Id -> AnnInfo SpecType -> Id -> Expr b -> (Calc.Expr -> Calc.Expr, (AppHead, [Calc.Reft]))
flattenCoreApp modId infTypes f e =
  let (hd, args) = apps e
      argsT = map (trans modId infTypes f) args
      (letBindersArgs, sArgs) = first (foldr (.) id) . unzip $ map toReft argsT
      (letBinderHd, appHd) =
        case hd of
          Var name -> (id, VarHead headSym)
            where
              headSym = case classifyHead . stripLegalName modId $ show name of
                HGeneric n | isDataConId name -> HDC n
                h -> h
          _ -> second ReftHead . toReft $ trans modId infTypes f hd
   in (letBinderHd . letBindersArgs, (appHd, sArgs))
  where
    apps :: Expr b -> (Expr b, [Expr b])
    apps (App tm1 tm2) = second (++ [tm2]) $ apps tm1
    apps tm = (tm, [])
    toReft :: Calc.Expr -> (Calc.Expr -> Calc.Expr, Calc.Reft)
    toReft (Calc.Reft t) = (id, t)
    toReft tm = (Calc.Let x Nothing tm, Calc.mkVar x)
      where
        x = "x_" ++ hashName tm

-- | Translate a flattened application to Calculus.
transFlattenedApp :: AppHead -> [Calc.Reft] -> Calc.Expr
transFlattenedApp (ReftHead h) args = Calc.Reft $ foldl Calc.App h args
transFlattenedApp (VarHead (HDC n)) args = Calc.Reft $ foldl Calc.App (Calc.DC n) args
transFlattenedApp (VarHead (HGeneric n)) args = Calc.Reft $ foldl Calc.App (Calc.mkVar n) args
transFlattenedApp (VarHead HNot) [tm] = Calc.Reft $ Calc.Neg tm
transFlattenedApp (VarHead (HBinOp op)) (_ : _ : a : b : _) = Calc.Reft $ Calc.Bop op a b
transFlattenedApp (VarHead (HConst tm)) _ = Calc.Reft tm
transFlattenedApp (VarHead HUnbox) [singleArg] = Calc.Reft singleArg
transFlattenedApp (VarHead HPatError) _ = Calc.Reft undefinedReft
transFlattenedApp (VarHead (HEqChain pop)) [_, fstTerm, lstTerm] = Calc.Reft $ Calc.Pop pop fstTerm lstTerm
transFlattenedApp (VarHead HCast) [_, tm, Calc.DC "QED"] =
  Calc.QMark (Calc.Reft Calc.unitTm) (Calc.Reft tm) Calc.ttTm
transFlattenedApp (VarHead HQmark) (_ : _ : firstArg : secondArg : _) =
  Calc.QMark (Calc.Reft firstArg) (Calc.Reft secondArg) Calc.ttTm
transFlattenedApp (VarHead HNot) args = Calc.Reft $ unexpected "not" args
transFlattenedApp (VarHead HLambda) args = Calc.Reft $ unexpected "lambda" args
transFlattenedApp (VarHead (HEqChain pop)) args = Calc.Reft $ unexpected (prettyShow pop) args
transFlattenedApp (VarHead HCast) args = Calc.Reft $ unexpected "***" args
transFlattenedApp (VarHead HQmark) args = Calc.Reft $ unexpected "?" args
transFlattenedApp (VarHead HUnbox) args = Calc.Reft $ unexpected "unbox" args
transFlattenedApp (VarHead (HBinOp _)) args = Calc.Reft $ unexpected "binop" args

unexpected :: Id -> [Calc.Reft] -> a
unexpected n as = error $ "transFlattenedApp: unexpected args for " ++ n ++ ": " ++ prettyShow as

transName :: Id -> Calc.Reft
transName "?" = error "Impossible: '?'"
transName n = M.findWithDefault (Calc.mkVar n) n SLH.builtinDCs

toStr :: (Data a) => a -> String
toStr = showConstr . toConstr

-- | Translate Haskell expressions.
-- The first argument is the name of the top-level binder we are translating.
-- Unsupported: casts, coercions, mutually recursive lets
-- Ignored: ticks
trans :: (CoreBinder b) => Id -> AnnInfo SpecType -> Id -> Expr b -> Calc.Expr
trans modId _ _ (Var n)
  | M.member strippedName SLH.builtinDCs = Calc.Reft $ transName strippedName
  | isDataConId n = Calc.Reft $ Calc.DC strippedName
  | otherwise =
      -- trace ("VAR: " ++ show n ++ " -> " ++ strippedName ++ " isDC=" ++ show (isDataConId n)) $
      Calc.Reft $ transName strippedName
  where
    strippedName = stripLegalName modId $ show n
trans modId infTypes f app@App {} = transApp modId infTypes f app
trans modId infTypes f (Case e _ _ alts) = transCase modId infTypes f e alts
trans modId infTypes f (Let bind e) = transLet modId infTypes f bind e
trans modId infTypes f (Tick _ e) = trans modId infTypes f e
trans _ _ _ (Type t) = transGHCType t
trans _ _ _ (Lit lit) = Calc.Reft $ transLit lit
trans _ _ _ c@Coercion {} = error $ "coercion expression not supported: " ++ toStr c
trans _ _ _ c@Cast {} = error $ "cast expression not supported: " ++ toStr c
trans _ _ _ l@(Lam {}) = error $ "lambda-abstraction outside of let-binding not supported: " ++ toStr l

-- | Translate type arguments.
transGHCType :: Type -> Calc.Expr
transGHCType (GHC.Core.TyCo.Rep.TyConApp tyCon []) = Calc.Reft (Calc.mkVar $ show tyCon)
transGHCType t = error $ "Polymorphism not supported: " ++ toStr t

-- | Translate applications by flattening them and translating the parsed application.
transApp :: (CoreBinder b) => Id -> AnnInfo SpecType -> Id -> Expr b -> Calc.Expr
transApp modId infTypes f app = letBinders $ transFlattenedApp appHead sArgs
  where
    (letBinders, (appHead, sArgs)) = flattenCoreApp modId infTypes f app

-- | Translate case expressions.
transCase :: (CoreBinder b) => Id -> AnnInfo SpecType -> Id -> Expr b -> [Alt b] -> Calc.Expr
transCase modId infTypes f e [] = trans modId infTypes f e
-- TODO: we now support match on simple terms, so change mkCase to support it
transCase modId infTypes f e alts = case eT of
  Calc.Reft (Calc.Var x' _ _) -> mkCase f x' branches
  Calc.Reft {} -> Calc.Let y Nothing eT (mkCase f y branches)
  _ -> error $ "unexpected case: case " ++ prettyShow eT ++ " of \n" ++ intercalate "\n" (map show branches)
  where
    eT = trans modId infTypes f e
    y = "x_" ++ hashName eT
    branches = map (altToClause modId infTypes f) alts

-- | Translate let bindings.
transLet :: (CoreBinder b) => Id -> AnnInfo SpecType -> Id -> Bind b -> Expr b -> Calc.Expr
transLet modId infTypes f bind body =
  let (x, ex) = deconstructBind bind
   in case ex of
        Lit {} -> trans modId infTypes f body -- ignore let lit (part of patError)
        _ ->
          -- Since λ-abstractions are encoded in lets, we simply rename the
          -- variables bound in the translated type using the names introduced
          -- by the λs in Core
          let (ys, ex') = collectLambdas ex
              tp = SLH.transType "" (SLH.ConstrArgsCtx Nothing []) $ binderType infTypes x
           in Calc.Let
                (stripLegalName modId $ show x)
                (Just $ Calc.renameParams ys tp)
                (trans modId infTypes f ex')
                (trans modId infTypes f body)
  where
    collectLambdas (Lam y e) = first ((stripLegalName modId $ show y) :) $ collectLambdas e
    collectLambdas e = ([], e)

-- | Trivial translation of literals
transLit :: Literal -> Calc.Reft
transLit (LitNumber _ n) = Calc.IntLit n
transLit (LitString s) = Calc.StringLit $ show s
transLit (LitFloat x) = Calc.FloatLit $ fromRational x
transLit (LitDouble x) = Calc.FloatLit $ fromRational x
transLit other = error $ "Unsupported literal " ++ toStr other

-- | Fall back to non-mutually recursive binds.
deconstructBind :: (NamedThing b) => Bind b -> (b, Expr b)
deconstructBind (NonRec b e) = (b, e)
deconstructBind (Rec [(b, e)]) = (b, e)
deconstructBind (Rec (_ : _)) = error "Found list of mutually recursive binders while translating."
deconstructBind (Rec []) = error "Found empty list of mutually recursive binders while translating."

-- | Retrieves the type inferred by Liquid Haskell for a variable
binderType :: (Show b, NamedThing b) => AnnInfo SpecType -> b -> SpecType
binderType (AI infTypes) x =
  case HM.lookup (getSrcSpan x) infTypes of
    Just [(Just qualifName, tp)] ->
      assert (Text.unpack (snd $ Text.breakOnEnd (Text.singleton '.') qualifName) == show x) tp
    _ -> error $ "Type annotation for " ++ show x ++ " not found."

-- | Straightforward translation of Haskell cases
altToClause :: (CoreBinder b) => Id -> AnnInfo SpecType -> Id -> Alt b -> Branch
altToClause modId infTypes f (Alt con bs e) =
  ((go con, map (\b -> (stripLegalName modId $ show b, False)) bs), Just (trans modId infTypes f e))
  where
    go :: AltCon -> String
    -- NOTE: was `show dc`, but no show instance for DataCon
    go (DataAlt dc) = stripLegalName modId $ showSDocUnsafe (ppr dc)
    go (LitAlt lit) = show (transLit lit)
    go DEFAULT = "_"

-- | Flattens and translate abstractions
--
-- > flattenFun(λx1. λx2.…λxn.e) = λx1…xn.trans(e)
flattenFun :: (CoreBinder b) => Id -> AnnInfo SpecType -> Id -> Expr b -> ([Id], Calc.Expr)
flattenFun modId infTypes f (Lam b e) = first ((stripLegalName modId . show) b :) $ flattenFun modId infTypes f e
flattenFun modId infTypes f e = ([], trans modId infTypes f e)

{- The following is based on code liquidhaskell-boot Transforms/CoreToLogic -}

-- | Cut redundant branches and matches and construct the given match
mkCase :: Id -> Id -> [Branch] -> Calc.Expr
mkCase f x = transCaseExpr (Just f) x False

collapseUnproductiveMatches :: Branch -> Branch
collapseUnproductiveMatches = modifyBrBody go
  where
    go e = case e of
      Calc.Case x branches b -> Calc.Case x (map collapseUnproductiveMatches branches) b
      _ -> e

-- | remove redundant branches/matches from a pattern match
transCaseExpr :: Maybe Id -> Id -> Bool -> [Branch] -> Calc.Expr
transCaseExpr = recurse []
  where
    recurse :: [(Id, (Id, [Id]))] -> Maybe Id -> Id -> Bool -> [Branch] -> Calc.Expr
    recurse prevPats fO indVar _ cases' =
      {- traceFuncRet ["recurse", show prevPats, show fO, indVar, show isRec, show cases] $ -}
      Calc.substs (map (\(x, r) -> (r, x)) substs) res
      where
        -- Replace occurrences of the induction variable with the constructor application in each branch
        cases =
          map
            ( \br ->
                let conApp = foldl Calc.App (Calc.DC (brCon br)) (map Calc.mkVar (brVars br))
                 in modifyBrBody (Calc.subst conApp indVar) br
            )
            cases'
        res = caseOrInduct indVar branches
        {- res = case branches of
          _ -> caseOrInduct indVar branches -}
        (cutCases, substs) = cutRedundantBranches indVar prevPats cases
        cleanedCases = map collapseUnproductiveMatches cutCases
        isRecursive :: Calc.Expr -> Bool
        isRecursive e = maybe False (`occursFreeIn` e) fO
        branches = map (modifyBrBody transBranchE) cleanedCases
        transBranchE :: Calc.Expr -> Calc.Expr
        transBranchE e = case e of
          Calc.Case (Calc.Var x _ _) css _ -> recurse prevPats fO x (isRecursive e) css
          Calc.Let x tpx def' tm -> Calc.Let x tpx (transBranchE def') (transBranchE tm)
          _ -> e
        caseOrInduct :: Id -> [Branch] -> Calc.Expr
        caseOrInduct x brs = Calc.Case (Calc.mkVar x) brs Nothing
    -- anyIsRec = if isRec || any (maybe False isRecursive . brBody) branches then Calc.Induct [] else Calc.Destruct

    -- \| Remove cases from nested matches whose patterns contradict the current branch's pattern in an ambient match
    cutRedundantBranches :: Id -> [(Id, (Id, [Id]))] -> [Branch] -> ([Branch], [(Id, Calc.Reft)])
    cutRedundantBranches n prevPats = second concat . unzip . cutBranches . filterBranches
      where
        filterBr br =
          ((n, (brCon br, brVars br)) `notElem` prevPats)
            || trace
              ( unwords
                  [ "cutting case: ",
                    show (brCon br, brVars br),
                    show (brBody br),
                    "from match on",
                    show n,
                    "due to redundancy with previous match patterns",
                    show prevPats
                  ]
              )
              False
        filterBranches = filter filterBr
        cutBranches :: [Branch] -> [(Branch, [(Id, Calc.Reft)])]
        cutBranches =
          mapMaybe
            ( \br -> case brBody br of
                Nothing -> Just (br, [])
                Just body ->
                  first (\body' -> ((brCon br, brVarsWithInd br), Just body'))
                    <$> cutRedundantMatches (prevPats ++ [(n, (brCon br, brVars br))]) body
            )

    -- \| Translate nested matches, replacing redundant matches with the translation of the only matching branch
    cutRedundantMatches :: [(Id, (Id, [Id]))] -> Calc.Expr -> Maybe (Calc.Expr, [(Id, Calc.Reft)])
    cutRedundantMatches prevPats (Calc.Case (Calc.Var m _ _) branches _) | m `elem` map fst prevPats = res
      where
        -- \| The previous pattern in which we already matched on the same variable as we do now, if any
        prevPat = find ((== m) . fst) prevPats
        -- \| Pattern and expression in the branch, in which the pattern matches the previous pattern, if any
        caseExpr = find ((== (fst . snd <$> prevPat)) . Just . brCon) branches
        caseVarSub = case (snd . snd <$> prevPat, brVars <$> caseExpr) of
          (Just args, Just args') -> newSubst
            where
              newSubst = mapMaybe mkSubstO (zip args args')
              mkSubstO (x, y) = case (unspecName x, unspecName y) of
                (True, False) -> Just (x, Calc.mkVar y) -- if variable is specified now, but not earlier use current name throughout
                (False, True) -> Just (y, Calc.mkVar x) -- if variable was specified before, but not now use previous name here as well
                (_, _) -> Nothing
              unspecName x = ("lq_anf" `isPrefixOf` x && all isDigit (removePrefix "lq_anf" x)) || "ds_d" `isPrefixOf` x
          _ -> []
        -- \| The translation of the only branch in which the pattern is consistent with the previously matched pattern matched against the same expression
        recO =
          ( \br -> case brBody br of
              Nothing -> Just (Calc.Reft undefinedReft, [])
              Just body -> cutRedundantMatches prevPats body
          )
            =<< caseExpr
        res = second (++ caseVarSub) <$> recO
    cutRedundantMatches prevPats (Calc.Case r@(Calc.Var m _ _) branches b) = Just (Calc.Case r branches' b, subs)
      where
        (branches', subs) = cutRedundantBranches m prevPats branches
    cutRedundantMatches _ tm = Just (tm, [])
