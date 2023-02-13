{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Haskell.Liquid.Synthesize.GHC where

import qualified Language.Fixpoint.Types       as F
import           Language.Haskell.Liquid.Types


import           Data.Default
import           Data.Maybe                     ( fromMaybe )
import           Liquid.GHC.TypeRep
import           Liquid.GHC.API                as GHC

import           Language.Fixpoint.Types
import qualified Data.HashMap.Strict           as M

import           Data.List
import           Data.List.Split

instance Default Type where
    def = TyVarTy alphaTyVar

mkVar :: Maybe String -> Int -> Type -> Var
mkVar x i t = mkGlobalVar VanillaId name t vanillaIdInfo
  where
    name = mkSystemName (mkUnique 'S' i) (mkVarOcc x')
    x'   = fromMaybe (freshName i) x

freshName :: Int -> String
freshName i = "lSyn$" ++ show i

-- | Assuming that the functions are instantiated when this function is called.
goalType ::  Type ->   --  This is the goal type. It is used for basic types.
              Type ->  --   This type comes from the environment.
              Bool     --   True if the 2nd arg produces expression 
                       --   of type equal to 1st argument.
goalType τ FunTy{ ft_res = t'' }
  | t'' == τ  = True
  | otherwise = goalType τ t''
goalType τ                 t
  | τ == t    = True
  | otherwise = False

-- Subgoals are function's arguments.
createSubgoals :: Type -> [Type]
createSubgoals (ForAllTy _ htype) = createSubgoals htype
createSubgoals (FunTy { ft_arg = t1, ft_res = t2 }) = t1 : createSubgoals t2
createSubgoals t                                    = [t]

subgoals :: Type ->               -- Given a function type,
            Maybe (Type, [Type])  -- separate the result type from the input types.
subgoals t = if null gTys then Nothing else Just (resTy, inpTys)
  where gTys            = createSubgoals t
        (resTy, inpTys) = (last gTys, take (length gTys - 1) gTys)


-- @withSubgoal@ :: Takes a subgoal type, and 
-- returns all expressions in @ExprMemory@ that have the same type.
withSubgoal :: [(Type, CoreExpr, Int)] -> Type -> [(CoreExpr, Int)]
withSubgoal []                  _ = []
withSubgoal ((t, e, i) : exprs) τ =
  if τ == t
    then (e, i) : withSubgoal exprs τ
    else withSubgoal exprs τ

-- | Assuming that goals are type variables or constructors.
--    Note: We maintain ordering from the goal type.
--    Not handled (compared to @varsInType): function types, type applications
unifyWith :: Type -> [Type]
unifyWith v@(TyVarTy _)   = [v]
unifyWith (TyConApp _ ts) = ts
unifyWith t               = error $ " [ unifyWith ] " ++ showTy t

fromAnf :: CoreExpr -> CoreExpr
fromAnf e = fst $ fromAnf' e []

-- | Replace let bindings in applications.
--   > If you find a binding add it to the second argument.
--                    | (lhs, rhs)      |
fromAnf'
  :: CoreExpr -> [(Var, CoreExpr)] -> (CoreExpr, [(Var, CoreExpr)])
fromAnf' (Lam b e) bnds
  = let (e', bnds') = fromAnf' e bnds
    in  (Lam b e', bnds')
  
fromAnf' (Let (NonRec rb lb) e) bnds
  | elem '#' (show rb) = let (lb', bnds') = fromAnf' lb bnds
                         in  fromAnf' e ((rb, lb') : bnds')

  | otherwise = (Let (NonRec rb lb') e', binds'')
  where
    (lb', bnds') = fromAnf' lb bnds
    (e', binds'') = fromAnf' e ((rb, lb') : bnds')

fromAnf' (Let (Rec {}) _) _ =
  error " By construction, no recursive bindings in let expression. "

fromAnf' (Var var) bnds
  = (fromMaybe (Var var) (lookup var bnds), bnds)

fromAnf' (Case scr bnd tp alts) bnds
  = (Case scr bnd tp (
        map (\(altc, xs, e) -> (altc, xs, fst $ fromAnf' e bnds))
          alts), bnds)

fromAnf' (App e1 e2) bnds
  = let (e1', bnds')  = fromAnf' e1 bnds
        (e2', bnds'') = fromAnf' e2 bnds'
    in  (App e1' e2', bnds'')

fromAnf' t@Type{} bnds = (t, bnds)

fromAnf' l@Lit{} bnds = (l, bnds)

fromAnf' (Tick _ e) bnds = fromAnf' e bnds

fromAnf' e _ = error $ "fromAnf: unsupported core expression "
               ++ F.showpp e

-- | Function used for pretty printing core as Haskell source.
--   Input does not contain let bindings.
coreToHs :: SpecType -> Var -> CoreExpr -> String
coreToHs _ v e = pprintSymbols (handleVar v
                                ++ " "
                                ++ pprintFormals caseIndent e [])

caseIndent :: Int
caseIndent = 2

indent :: Int -> String
indent i = replicate i ' '

symbols :: String
symbols = [':']

pprintSymbols :: String -> String
pprintSymbols txt =
  foldr (\x xs -> pprintSym symbols x ++ "\n" ++ xs) [] $
  splitOn "\n" txt

pprintSym :: String -> String -> String
pprintSym symbols s
  | [] <- suffix = s 
  | (c:cs) <- suffix =
    case find (== c) symbols of
      Nothing -> s
      Just s' -> prefix ++ ['(', s', ')'] ++ cs
      where 
        prefix = takeWhile (== ' ') s
        suffix = dropWhile (== ' ') s

pprintFormals :: Int -> CoreExpr -> [Var] -> String
pprintFormals i e vs = handleLam "= " i e vs

handleLam :: String -> Int -> CoreExpr -> [Var] -> String
handleLam char i (Lam v e) vs
  | isTyVar   v = " {- tyVar -}"     ++ handleLam char i e vs
  | isTcTyVar v = " {- isTcTyVar -}" ++ handleLam char i e vs
  | isTyCoVar v = " {- isTyCoVar -}" ++ handleLam char i e vs
  | isCoVar   v = " {- isCoVar -}"   ++ handleLam char i e vs
  | isId      v = handleVar v ++ " " ++ handleLam char i e vs  
  | otherwise   = handleVar v ++ " " ++ handleLam char i e vs
handleLam char i e vs = char ++ pprintBody vs i e

----------------------------------------------------------------------
{- Helper functions for print body -}

-- handleWiredIn :: Name -> String
-- handleWiredIn w
--   | getLocaln w == "I#" = "{- " ++ show w ++ " -}"
--   {-
--     Excluding GHC.Types also excludes Boolean values,
--     "GHC.Type.True" on RConstantTimeComparison for
--     example.
-- 
--     getModule w == "GHC.Types" = "{- " ++ show w ++ " -}"
--   -}
--   | otherwise                  = getLocaln w
--   where
--     -- getModule :: Name -> String
--     -- getModule n = moduleNameString (moduleName $ nameModule n)

{- If a specific function is built-in into haskell it will still
contain a module. To remove it and print it properly we localise
the name first. -}
getLocalName :: Name -> String
getLocalName n = getOccString (localiseName n)

getExternalName :: Name -> String
getExternalName n = mod ++ outName
  where
    outName = getOccString n
    mod     = case nameModule_maybe n of
                Just m  -> (moduleNameString $ moduleName m) ++ "."
                Nothing -> ""

{- Handle the multiple types of variables one might encounter
in Haskell. -}
handleVar :: Var -> String
handleVar v
  | isTyConName     name = "{- TyConName -}"
  | isTyVarName     name = "{- TyVar -}"
  | isSystemName    name = show name
--                           ++ "{- SysName -}"
  | isWiredInName   name = getLocalName name
--                           ++ "{- WiredInName -}"
  | isExternalName  name = getExternalName name
                           ++ "{- external name -}"
  | isInternalName  name = getOccString name
--                           ++ "{- Internal -}"
  | otherwise            = "{- Not properly handled -}"
                           ++ show name
  where
    name :: Name
    name = varName v

{- Should not be done here, but function used to check if is an
undesirable variable or not (I#) -}
undesirableVar :: Var -> Bool
undesirableVar v
  | getOccString (localiseName (varName v)) == "I#" = True
  | otherwise = False
----------------------------------------------------------------------

pprintBody :: [Var] -> Int -> CoreExpr -> String
pprintBody vs i e@(Lam {})
  = "(\\" ++ handleLam " -> " i e vs ++ ")"

pprintBody vs _ (Var v)
  | elem v vs = ""
  | otherwise = handleVar v

pprintBody vs i (App e (Type{})) = pprintBody vs i e

pprintBody vs i (App (Var v) e2)
  | undesirableVar v = pprintBody vs i e2
  | otherwise        = "" ++ left ++ "\n"
                       ++ indent (i + 1)
                       ++ "(" ++ right ++ ")"
  where
    left  = handleVar v
    right = pprintBody vs (i+1) e2
    
pprintBody vs i (App e1 e2) = "(" ++ left ++ ")\n"
                              ++ indent (i + 1)
                              ++ "(" ++ right ++ ")"
  where
    left  = pprintBody vs i e1
    right = pprintBody vs (i+1) e2

pprintBody _ _ l@(Lit literal) =
  case isLitValue_maybe literal of
    Just i   -> show i
    Nothing  -> "{- Lit is not LitChar or LitNumber -}" ++ show l      

pprintBody vs i (Case e _ _ alts)
  = "case " ++ pprintBody vs i e ++ " of"
  ++ concatMap (pprintAlts vs (i + caseIndent)) alts

pprintBody _ _ Type{}
  = "{- Type -}"

pprintBody vs i (Let (NonRec x e1) e2) =
  "\n" ++ indent i ++
  "let " ++ handleVar x ++ " = ("
  ++ pprintBody vs newIdent e1 ++ ") in " ++
  pprintBody vs newIdent e2
  where
    newIdent :: Int
    newIdent = i + 5
    
pprintBody _ _ (Let (Rec {}) _) = "{- let rec -}"

pprintBody _ _ e
  = error (" Not yet implemented for e = " ++ show e)

{-
data Alt Var = Alt AltCon [Var] (Expr Var)

data AltCon = DataAlt DataCon
            | LitAlt  Literal
            | DEFAULT
-}
pprintAlts :: [Var] -> Int -> Alt Var -> String
pprintAlts vars i (DataAlt dataCon, vs, e)
  = "\n" ++ indent i
  ++ getOccString (getName dataCon)
  ++ concatMap (\v -> " " ++ handleVar v) vs
  ++ " -> " ++ pprintBody vars (i+caseIndent) e
pprintAlts _ _ _ =
  error " Pretty printing for pattern match on datatypes. "



-----------------------------------------------------------------------------------
--  |                          Prune trivial expressions                       | --
-----------------------------------------------------------------------------------
nonTrivial :: GHC.CoreExpr -> Bool
nonTrivial (GHC.App _ (GHC.Type _)) = False
nonTrivial _                        = True

nonTrivials :: [GHC.CoreExpr] -> Bool
nonTrivials = foldr (\x b -> nonTrivial x || b) False

trivial :: GHC.CoreExpr -> Bool
trivial (GHC.App (GHC.Var _) (GHC.Type _)) = True -- Is this a nullary constructor?
trivial _ = False

hasTrivial :: [GHC.CoreExpr] -> Bool
hasTrivial es = foldr (\x b -> trivial x || b) False es

allTrivial :: [[GHC.CoreExpr]] -> Bool
allTrivial es = foldr (\x b -> hasTrivial x && b) True es

rmTrivials :: [(GHC.CoreExpr, Int)] -> [(GHC.CoreExpr, Int)]
rmTrivials = filter (not . trivial . fst)

----------------------------------------------------------------------------------
--  |                        Scrutinee filtering                              | --
----------------------------------------------------------------------------------

isVar :: GHC.CoreExpr -> Bool
isVar (GHC.Var _) = True
isVar _           = False

returnsTuple :: Var -> Bool
returnsTuple v =
  case subgoals (varType v) of
    Nothing      -> False
    Just (t, _) ->
      case t of
        TyConApp c _ts -> c == pairTyCon
        _              -> False

------------------------------------------------------------------------------------------------
-------------------------------------- Handle REnv ---------------------------------------------
------------------------------------------------------------------------------------------------
-- Duplicate from Monad due to dependencies between modules.
type SSEnv = M.HashMap Symbol (SpecType, Var)

filterREnv :: M.HashMap Symbol SpecType -> M.HashMap Symbol SpecType
filterREnv renv =
  let renv_lst  = M.toList renv
      renv_lst' = filter (\(_, specT) ->  let ht = toType False specT
                                          in  showTy ht /= "(RApp   GHC.Prim.Addr# )") renv_lst
  in  M.fromList renv_lst'

getTopLvlBndrs :: GHC.CoreProgram -> [Var]
getTopLvlBndrs = concatMap (\case GHC.NonRec b _ -> [b]
                                  GHC.Rec recs   -> map fst recs)

-- | That' s a hack to get the type variables we need for instantiation.
getUniVars :: GHC.CoreProgram -> Var -> ([Var], [Var])
getUniVars cp tlVar =
  case filter (`isInCB` tlVar) cp of
    [cb] -> getUniVars0 (getBody cb tlVar) ([], [])
    _    -> error " Every top-level corebind must be unique! "

getUniVars0 :: GHC.CoreExpr -> ([Var], [Var]) -> ([Var], [Var])
getUniVars0 (Lam b e) (uvs, tcDicts)
  = case varType b of
      TyConApp c _ ->
        if isClassTyCon c
          then getUniVars0 e (uvs, b : tcDicts)
          else getUniVars0 e (b:uvs, tcDicts)
      _ -> getUniVars0 e (b:uvs, tcDicts)
getUniVars0 _ vs
  = vs

getBody :: GHC.CoreBind -> Var -> GHC.CoreExpr
getBody (GHC.NonRec b e) tlVar = if b == tlVar then e else error " [ getBody ] "
getBody (GHC.Rec _)   _ = error "Assuming our top-level binder is non-recursive (only contains a hole)"

--                       | Current top-level binder |
varsP :: GHC.CoreProgram -> Var -> (GHC.CoreExpr -> [Var]) -> [Var]
varsP cp tlVar f =
  case filter (`isInCB` tlVar) cp of
    [cb] -> varsCB cb f
    _    -> error " Every top-level corebind must be unique! "

isInCB :: GHC.CoreBind -> Var -> Bool
isInCB (GHC.NonRec b _) tlVar = b == tlVar
isInCB (GHC.Rec recs) tlVar   = foldr ((\v b -> v == tlVar && b) . fst) True recs

varsCB :: GHC.CoreBind -> (GHC.CoreExpr -> [Var]) -> [Var]
varsCB (GHC.NonRec _ e) f = f e
varsCB (GHC.Rec _) _ = notrace " [ symbolToVarCB ] Rec " []

varsE :: GHC.CoreExpr -> [Var]
varsE (GHC.Lam a e) = a : varsE e
varsE (GHC.Let (GHC.NonRec b _) e) = b : varsE e
varsE (GHC.Case _ b _ alts) = foldr (\(_, vars, e) res -> vars ++ varsE e ++ res) [b] alts
varsE (GHC.Tick _ e) = varsE e
varsE _ = []

caseVarsE :: GHC.CoreExpr -> [Var]
caseVarsE (GHC.Lam _ e) = caseVarsE e
caseVarsE (GHC.Let (GHC.NonRec _ _) e) = caseVarsE e
caseVarsE (GHC.Case _ b _ alts) = foldr (\(_, _, e) res -> caseVarsE e ++ res) [b] alts
caseVarsE (GHC.Tick _ e) = caseVarsE e
caseVarsE _ = []

instance Default Var where
  def = alphaTyVar

symbolToVar :: GHC.CoreProgram -> Var -> M.HashMap Symbol SpecType -> SSEnv
symbolToVar cp tlBndr renv =
  let vars = [(F.symbol x, x) | x <- varsP cp tlBndr varsE]
      casevars = [F.symbol x | x <- varsP cp tlBndr caseVarsE]
      tlVars = [(F.symbol x, x) | x <- getTopLvlBndrs cp]
      lookupErrorMsg x = " [ symbolToVar ] impossible lookup for x = " ++ show x
      symbolVar x = fromMaybe (fromMaybe (error (lookupErrorMsg x)) $ lookup x tlVars) $ lookup x vars
      renv' = foldr M.delete renv casevars
  in  M.fromList [ (s, (t, symbolVar s)) | (s, t) <- M.toList renv']

argsP :: GHC.CoreProgram -> Var -> [Var]
argsP []         tlVar = error $ " [ argsP ] " ++ show tlVar
argsP (cb : cbs) tlVar
  | isInCB cb tlVar = argsCB cb
  | otherwise = argsP cbs tlVar

argsCB :: GHC.CoreBind -> [Var]
argsCB (GHC.NonRec _ e) = argsE e
argsCB _                = error " [ argsCB ] "

argsE :: GHC.CoreExpr -> [Var]
argsE (GHC.Lam a e) = a : argsE e
argsE (GHC.Let (GHC.NonRec _ _) e) = argsE e
argsE _ = []

notrace :: String -> a -> a
notrace _ a = a

