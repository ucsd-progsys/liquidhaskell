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
        map (\(altc, xs, e) ->
               (altc, xs, fst $ fromAnf' e bnds)) alts), bnds)

fromAnf' (App e1 e2) bnds
  = let (e1', bnds')  = fromAnf' e1 bnds
        (e2', bnds'') = fromAnf' e2 bnds'
    in  (App e1' e2', bnds'')

fromAnf' t@Type{} bnds = (t, bnds)

fromAnf' (Lit (GHC.LitString _)) bnds = (GHC.unitExpr, bnds)

fromAnf' l@Lit{} bnds = (l, bnds)

fromAnf' (Tick s e) bnds = (Tick s e', bnds')
  where
    (e', bnds') = fromAnf' e bnds

fromAnf' e _ = error $ "fromAnf: unsupported core expression "
               ++ F.showpp e

-- | Function used for pretty printing core as Haskell source.
--   Input does not contain let bindings.
coreToHs :: SpecType -> Var -> CoreExpr -> String
coreToHs _ v e = pprintSymbols (handleVar v
                                ++ " "
                                ++ pprintFormals caseIndent e)

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

pprintFormals :: Int -> CoreExpr -> String
pprintFormals i e = handleLam "= " i e

handleLam :: String -> Int -> CoreExpr -> String
handleLam char i (Lam v e)
  | isTyVar   v = " {- tyVar -}"     ++ handleLam char i e
  | isTcTyVar v = " {- isTcTyVar -}" ++ handleLam char i e
  | isTyCoVar v = " {- isTyCoVar -}" ++ handleLam char i e
  | isCoVar   v = " {- isCoVar -}"   ++ handleLam char i e
  | isId      v = handleVar v ++ " " ++ handleLam char i e  
  | otherwise   = handleVar v ++ " " ++ handleLam char i e
handleLam char i e = char ++ pprintBody i e


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
                Just m  -> checkUnitReturn m (unitComment m)
                Nothing -> ""
    
    unitComment :: Module -> String
    unitComment m = unitIdString (moduleUnitId m)

    checkUnitReturn :: Module -> String -> String
    checkUnitReturn _ "base" = ""
    checkUnitReturn m _      = moduleNameString (moduleName m) ++ "."


{- Handle the multiple types of variables one might encounter
in Haskell. -}
handleVar :: Var -> String
handleVar v
  | isTyConName     name = "{- TyConName -}"
  | isTyVarName     name = "{- TyVar -}"
  | isSystemName    name = getSysName name
--                           ++ "{- SysName -}"
  | isWiredInName   name = getLocalName name
--                           ++ "{- WiredInName -}"
  | isInternalName  name = show name
--                           ++ "{- Internal -}"
  | isExternalName  name = getExternalName name
--                           ++ "{- external name -}"
  | otherwise            = "{- Not properly handled -}"
                           ++ show name
  where
    name :: Name
    name = varName v


getSysName :: Name -> String
getSysName n
  | elem '#' occ = head (splitOn "$##" occ)
                   ++ show num ++ "_" ++ [tag]
  | otherwise      = show n
  where
    (tag, num) = unpkUnique $ getUnique n
    occ        = getOccString n
{- Should not be done here, but function used to check if is an
undesirable variable or not (I#) -}
undesirableVar :: CoreExpr -> Bool
undesirableVar (Var v)
  | getOccString (localiseName (varName v)) == "I#" = True
  | otherwise = False
undesirableVar _ = False

checkUnit :: CoreExpr -> Bool
checkUnit (Var v)
  | getOccString (localiseName (varName v)) == "()" = True
  | otherwise = False
checkUnit _ = False  
----------------------------------------------------------------------
pprintBody' :: CoreExpr -> String
pprintBody' = pprintBody 0

pprintBody :: Int -> CoreExpr -> String
pprintBody i e@(Lam {}) = "(\\" ++ handleLam " -> " i e ++ ")"

pprintBody _ var@(Var v)
  | undesirableVar var = ""
  | otherwise          = handleVar v

pprintBody i (App e Type{}) = pprintBody i e
    
pprintBody i (App e1 e2)
  | undesirableVar e1 = pprintBody i e2
  | undesirableVar e2 = pprintBody i e1
  | checkUnit e2      = pprintBody i e1
                        ++ " "
                        ++ pprintBody i e2
  | otherwise = "(" ++ left ++ ")\n"
                ++ indent (i + 1)
                ++ "(" ++ right ++ ")"
  where
    left  = pprintBody i e1
    right = pprintBody (i+1) e2

pprintBody _ l@(Lit literal) =
  case isLitValue_maybe literal of
    Just i   -> show i
    Nothing  -> show l

pprintBody i (Case e _ _ alts)
  = "case " ++ pprintBody i e ++ " of"
  ++ concatMap (pprintAlts (i + caseIndent)) alts

pprintBody _ Type{} = "{- Type -}"

pprintBody i (Let (NonRec x e1) e2) =
  letExp ++
  eqlExp ++
  indent i ++ pprintBody (i+1) e2
  where
    letExp      = "let " ++ handleVar x ++ " = "
    eqlExp      = pprintBody firstIdent e1 ++ " in\n"
    firstIdent  = i + caseIndent*2 + length letExp
    
pprintBody _ (Let Rec{} _) = "{- let rec -}"

pprintBody i (Tick (SourceNote _ s) e)
  | expr == "()" = "{- " ++ s ++ " -} " ++ expr
  | otherwise    = "{- " ++ s ++ " -}"
                   ++ "\n" ++ indent i
                   ++ expr
  where
    expr = pprintBody i e

pprintBody i (Tick _ e) = pprintBody i e

pprintBody _ e = error (" Not yet implemented for e = " ++ show e)

{-
data Alt Var = Alt AltCon [Var] (Expr Var)

data AltCon = DataAlt DataCon
            | LitAlt  Literal
            | DEFAULT
-}
pprintAlts :: Int -> Alt Var -> String
pprintAlts i (DataAlt dataCon, vs, e)
  = "\n" ++ indent i
    ++ elCase
    ++ pprintBody (i + newIndent) e
  where
    elCase = getOccString (getName dataCon)
             ++ concatMap (\v -> " " ++ handleVar v) vs
             ++ " -> "
    newIndent = length elCase
    
pprintAlts _ _ =
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

