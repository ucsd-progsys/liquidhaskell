{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Language.Haskell.Liquid.Synthesize.GHC where

import qualified Language.Fixpoint.Types       as F
import           Language.Haskell.Liquid.Types
import           Data.Default
import           Data.Maybe                     ( fromMaybe )
import           Language.Haskell.Liquid.GHC.TypeRep
import           Language.Haskell.Liquid.GHC.API as GHC
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
fromAnf' :: CoreExpr -> [(Var, CoreExpr)] -> (CoreExpr, [(Var, CoreExpr)])
fromAnf' (Lam b e) bnds
  = let (e', bnds') = fromAnf' e bnds
    in  (Lam b e', bnds')
fromAnf' (Let bnd e) bnds
  = case bnd of Rec {}       -> error " By construction, no recursive bindings in let expression. "
                NonRec rb lb -> let (lb', bnds') = fromAnf' lb bnds
                                in  fromAnf' e ((rb, lb') : bnds')
fromAnf' (Var var) bnds 
  = (fromMaybe (Var var) (lookup var bnds), bnds)
fromAnf' (Case scr bnd tp alts) bnds
  = (Case scr bnd tp (map (\(altc, xs, e) -> (altc, xs, fst $ fromAnf' e bnds)) alts), bnds)
fromAnf' (App e1 e2) bnds
  = let (e1', bnds')  = fromAnf' e1 bnds 
        (e2', bnds'') = fromAnf' e2 bnds'
    in  (App e1' e2', bnds'')
fromAnf' t@Type{} bnds 
  = (t, bnds)
fromAnf' l@Lit{} bnds 
  = (l, bnds)
fromAnf' _ _
  = error " Should not reach this point. "

-- | Function used for pretty printing core as Haskell source.
--   Input does not contain let bindings.
coreToHs :: SpecType -> Var -> CoreExpr -> String
coreToHs t v e = pprintSymbols (discardModName v ++ pprintFormals caseIndent v e (tracepp " cnt " cnt) [])
  where cnt = countTcConstraints t

symbols :: String
symbols = [':']

pprintSymbols :: String -> String
pprintSymbols txt = foldr (\x xs -> pprintSym symbols x ++ xs) [] txt

pprintSym :: String -> Char -> String
pprintSym symbols' s
  = case find (== s) symbols' of
      Nothing -> [s]
      Just s' -> ['(', s', ')']

discardModName :: Var -> String
discardModName v = last (splitOn "." (show v))

rmModName :: String -> String
rmModName s = 
  let ts = splitOn "." s
  in  maintainLParen ts ++ last ts ++ maintainRParen ts

maintainLParen :: [String] -> String
maintainLParen ts 
  = if length ts > 1 && head (head ts) == '('
      then  "("
      else  ""

maintainRParen :: [String] -> String
maintainRParen ts 
  = if last (last ts) == '('
      then  ")"
      else  ""

pprintFormals :: Int -> Var -> CoreExpr -> Int -> [Var] -> String
pprintFormals i v (Lam b e) cnt vs
  = if isTyVar b
      then pprintFormals i v e cnt vs
      else  if cnt > 0 
              then  pprintFormals i v e (cnt - 1) (b:vs)
              else  " " ++ show b ++ pprintFormals i v e cnt vs
pprintFormals i _ e _ vs
  = " =" ++ pprintBody vs i e

caseIndent :: Int 
caseIndent = 4

indent :: Int -> String
indent i = replicate i ' '

errorExprPp :: CoreExpr -> Bool
errorExprPp (GHC.App (GHC.App err'@(GHC.Var _) (GHC.Type _)) _)
  = show err' == "Language.Haskell.Liquid.Synthesize.Error.err"
errorExprPp _ 
  = False

pprintVar :: Var -> String 
pprintVar v = if isTyVar v then "" else " " ++ discardModName v

pprintBody :: [Var] -> Int -> CoreExpr -> String
pprintBody vs i (Lam b e) 
  = pprintFormals i b e 0 vs
pprintBody vs _ (Var v)
  = case find (== v) vs of 
      Nothing -> pprintVar v
      Just _  -> ""
pprintBody vs _ e@App{}
  = let pprintApp = fixApplication (show e)
        noTcVars  = filter (\x -> case find (== x) (map show vs) of 
                                    Nothing -> True
                                    Just _  -> False) (words pprintApp)
    in  if errorExprPp e
          then " error \" Dead code! \" "
          else " " ++ unwords noTcVars
pprintBody _ _ l@Lit{}
  = " " ++ show l
pprintBody vs i (Case scr _ _ alts)
  = "\n" ++ indent i ++ 
    "case" ++ pprintBody vs i scr ++ " of\n" ++ 
    concatMap (pprintAlts vs (i + caseIndent)) alts 
pprintBody _ _ Type{} 
  = ""
pprintBody _ _ e
  = error (" Not yet implemented for e = " ++ show e)

fixApplication :: String -> String
fixApplication e = 
  let ws' = words (replaceNewLine e)
      ws = handleCommas ws'
      cleanWs = rmTypeAppl ws
  in  unwords (fixCommas $ fixParen (map rmModName cleanWs))

handleCommas :: [String] -> [String]
handleCommas [] = []
handleCommas (c:cs)
  = if last c == ','
      then init c : "," : handleCommas cs
      else c : handleCommas cs

fixCommas :: [String] -> [String]
fixCommas [] = []
fixCommas [x] = [x]
fixCommas (x:y:xs)
  = if y == ","
      then (x++y) : fixCommas xs
      else x : fixCommas (y:xs)

fixParen :: [String] -> [String]
fixParen [] = []
fixParen [x] = [x]
fixParen (x:y:xs) 
  = if replicate (length y) ')' == y
      then  let w0 = x ++ y 
                w = if head w0 == '(' && last w0 == ')' 
                      then tail (init w0) 
                      else w0
            in  w : fixParen xs
      else x : fixParen (y:xs)

rmTypeAppl :: [String] -> [String]
rmTypeAppl [] 
  = []
rmTypeAppl (c:cs) 
  = if c == "@"
      then  case cs of 
              [] -> error " Type application: Badly formatted string. "
              (c': cs') -> 
                let p = paren c'
                in  if null p then rmTypeAppl cs' else p : rmTypeAppl cs'
      else c:rmTypeAppl cs

paren :: String -> String 
paren [] 
  = []
paren (c:cs) 
  = if c == ')' then c : paren cs else paren cs

replaceNewLine :: String -> String
replaceNewLine [] 
  = []
replaceNewLine (c:cs) 
  = if c == '\n' 
      then ' ' : replaceNewLine cs 
      else c : replaceNewLine cs

pprintAlts :: [Var] -> Int -> Alt Var -> String
pprintAlts vars i (DataAlt dataCon, vs, e)
  = indent i ++ show dataCon ++ concatMap (\v -> " " ++ show v) vs ++ " ->" ++ 
    pprintBody vars (i+caseIndent) e ++ "\n"
pprintAlts _ _ _
  = error " Pretty printing for pattern match on datatypes. "

-- TODO Remove variables generated for type class constraints
countTcConstraints :: SpecType -> Int
countTcConstraints t = 
  let ws = words (show t)

      countCommas :: [String] -> Int
      countCommas []     = 0
      countCommas (x:xs) = 
        case find (== ',') x of
          Nothing -> countCommas xs
          Just _  -> 1 + countCommas xs

  in  case find (== "=>") ws of
        Nothing -> 0
        Just _  -> 1 + countCommas (takeWhile (/= "=>") ws)
  


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
  case filter (\cb -> isInCB cb tlVar) cp of
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
