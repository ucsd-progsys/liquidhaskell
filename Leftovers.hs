
------------------------------------------------------------------------------------
-- ??? Qualifiers.hs [specificationQualifiers]
------------------------------------------------------------------------------------

module SpecQuals (specificationQualifiers) where

import Language.Fixpoint.Misc
import Control.DeepSeq
import Control.Applicative      ((<$>))
import Data.List                (delete, nub)
import Data.Maybe               (fromMaybe)
import qualified Data.HashSet as S
import Data.Bifunctor           (second) 

specificationQualifiers :: GhcInfo -> [Qualifier] 

specificationQualifiers info  
  = [ q | (x, t) <- tySigs $ spec info, x `S.member` xs, q <- refTypeQuals tce t
    ] where xs  = S.fromList $ defVars info
            tce = tcEmbeds   $ spec info

refTypeQuals tce t 
  = quals ++ 
    [ pAppQual tce p args (v, expr) 
    | p            <- preds
    , (s, v, _)    <- pargs p
    , (args, expr) <- concatMap (expressionsOfSort (rTypeSort tce s)) quals
    ]  where quals       = refTypeQuals' tce t
             preds       = snd3 $ bkUniv t

expressionsOfSort sort (Q _ pars (PAtom Eq (EVar v) e2)) | (v, sort) `elem` pars
  = [(filter (/=(v, sort)) pars, e2)]
expressionsOfSort _ _  = [] 

pAppQual tce p args (v, expr)
  =  Q "Auto" freeVars pred
  where freeVars = (vv, tyvv):(predv,typred):args
        pred     = pApp predv $ EVar vv:predArgs
        vv       = S "v"
        predv    = S "~P"
        tyvv     = rTypeSort tce $ ptype p
        typred   = rTypeSort tce (toPredType p :: RRType ())
        predArgs = mkexpr <$> (snd3 <$> pargs p)
        mkexpr x | x == v    = expr
                 | otherwise = EVar x

-- refTypeQuals :: SpecType -> [Qualifier] 
refTypeQuals' tce t0 = go emptySEnv t0
  where go γ t@(RVar _ _)         = refTopQuals tce t0 γ t     
        go γ (RAllT _ t)          = go γ t 
        go γ (RAllP _ t)          = go γ t 
        go γ (RFun x t t' _)      = (go γ t) ++ (go (insertSEnv x (rTypeSort tce t) γ) t')
        go γ t@(RApp _ ts _ _)    = (refTopQuals tce t0 γ t) ++ concatMap (go (insertSEnv (rTypeValueVar t) (rTypeSort tce t) γ)) ts
        go γ (REx x t t' )        = (go γ t) ++ (go (insertSEnv x (rTypeSort tce t) γ) t')
        go _ _                    = []

refTopQuals tce t0 γ t 
  = [ mkQual t0 γ v so pa | let (RR so (Reft (v, ras))) = rTypeSortedReft tce t 
                          , RConc p                    <- ras                 
                          , pa                         <- atoms p
    ] ++
    [ mkPQual tce t0 γ s e | let (U _ (Pr ps)) = fromMaybe (msg t) $ stripRTypeBase t
                           , p <- (findPVar (snd3 (bkUniv t0))) <$> ps
                           , (s, _, e) <- pargs p
    ] where msg t = errorstar $ "Qualifier.refTopQuals: no typebase" ++ showPpr t

mkPQual tce t0 γ t e = mkQual t0 γ' v so pa
  where v = S "vv"
        so = rTypeSort tce t
        γ' = insertSEnv v so γ
        pa = PAtom Eq (EVar v) e   

mkQual t0 γ v so p = Q "Auto" ((v, so) : yts) p'
  where yts  = [(y, lookupSort t0 x γ) | (x, y) <- xys ]
        p'   = subst (mkSubst (second EVar <$> xys)) p
        xys  = zipWith (\x i -> (x, S ("~A" ++ show i))) xs [0..] 
        xs   = delete v $ orderedFreeVars γ p

lookupSort t0 x γ = fromMaybe (errorstar msg) $ lookupSEnv x γ 
  where msg = "Unknown freeVar " ++ show x ++ " in specification " ++ show t0

orderedFreeVars γ = nub . filter (`memberSEnv` γ) . syms 

-- orderedFreeVars   :: Pred -> [Symbol]
-- orderedFreeVars p = nub $ everything (++) ([] `mkQ` f) p
--   where f (EVar x) = [x]
--         f _        = []


-- atoms' ps = traceShow ("atoms: ps = " ++ showPpr ps) $ atoms ps
atoms (PAnd ps) = concatMap atoms ps
atoms p         = [p]


------------------------------------------------------
-- Liquid.hs
------------------------------------------------------

cgInfoFInfo :: CGInfo -> FInfo
cgInfoFInfo cgi = FI (M.fromList $ addIds $ fixCs cgi) 
                     (fixWfs    cgi) 
                     (binds     cgi) 
                     (globals   cgi) 
                     (lits      cgi) 
                     (kuts      cgi)  
                     (specQuals cgi)
 

----------------------------------------------------------------
----- Parse.hs
----------------------------------------------------------------

module Language.Haskell.Liquid.Parse (
  hsSpecificationP
  ) where

import Data.List (partition)
import Language.Haskell.Liquid.RefType
import qualified Language.Haskell.Liquid.Measure as Measure
import Outputable (showPpr)
import Language.Haskell.Liquid.FileNames (listConName, propConName, tupConName)

braces     = Token.braces     lexer
angles     = Token.angles     lexer
dot        = Token.dot        lexer

tyVarIdP :: Parser String
tyVarIdP = condIdP alphanums (isLower . head) 
           where alphanums = ['a'..'z'] ++ ['0'..'9']

-- | The top-level parser for "bare" refinement types. If refinements are
-- not supplied, then the default "top" refinement is used.

bareTypeP :: Parser BareType 

bareTypeP   
  =  try bareFunP
 <|> bareAllP
 <|> bareExistsP
 <|> bareAtomP 
 
bareArgP 
  =  bareAtomP  
 <|> parens bareTypeP

bareAtomP 
  =  frefP bbaseP 
 <|> try (dummyP (bbaseP <* spaces))

bbaseP :: Parser (FReft -> BareType)
bbaseP 
  =  liftM2 bLst (brackets bareTypeP) predicatesP
 <|> liftM2 bTup (parens $ sepBy bareTypeP comma) predicatesP
 <|> try (liftM2 bAppTy lowerIdP bareTyArgP)
 <|> try (liftM2 bRVar lowerIdP monoPredicateP)
 <|> liftM3 bCon upperIdP predicatesP (sepBy bareTyArgP blanks)

bbaseNoAppP :: Parser (FReft -> BareType)
bbaseNoAppP
  =  liftM2 bLst (brackets bareTypeP) predicatesP
 <|> liftM2 bTup (parens $ sepBy bareTypeP comma) predicatesP
 <|> try (liftM3 bCon upperIdP predicatesP (return []))
 <|> liftM2 bRVar lowerIdP monoPredicateP 

bareTyArgP 
  =  try (braces $ (liftM RExprArg exprP))
 <|> try bareAtomNoAppP
 -- <|> braces (liftM RExprArg exprP) -- ^ braces needed to distinguish tyvar from evar args
 <|> try (parens bareTypeP)
 -- <|> try (liftM RExprArg exprP) 
 -- <|> liftM RExprArg (parens exprP) 

bareAtomNoAppP 
  =  frefP bbaseNoAppP 
 <|> try (dummyP (bbaseNoAppP <* spaces))

bareExistsP 
  = do reserved "exists"
       zs <- brackets $ sepBy1 exBindP comma 
       dot
       t  <- bareTypeP
       return $ foldr (uncurry REx) t zs
     
exBindP 
  = xyP binderP colon bareTypeP 
  

bareAllP 
  = do reserved "forall"
       as <- many tyVarIdP -- sepBy1 tyVarIdP comma
       ps <- predVarDefsP
       dot
       t  <- bareTypeP
       return $ foldr RAllT (foldr RAllP t ps) as

predVarDefsP 
  =  try (angles $ sepBy1 predVarDefP comma)
 <|> return []

predVarDefP
  = liftM3 bPVar predVarIdP dcolon predVarTypeP

predVarIdP 
  = stringSymbol <$> tyVarIdP

bPVar p _ xts  = PV p τ τxs 
  where (_, τ) = last xts
        τxs    = [ (τ, x, EVar x) | (x, τ) <- init xts ]

predVarTypeP :: Parser [(Symbol, BSort)]
predVarTypeP = do t <- bareTypeP
                  let (xs, ts, t') = bkArrow $ thd3 $ bkUniv $ t
                  if isPropBareType t' 
                    then return $ zip xs (toRSort <$> ts) 
                    else parserFail $ "Predicate Variable with non-Prop output sort: " ++ showPpr t

-- predVarTypeP 
--   =  try ((liftM (: []) predVarArgP) <* reserved "->" <* reserved boolConName)
--  <|> liftM2 (:) predVarArgP (reserved "->" >> predVarTypeP)

-- predVarArgP = xyP argP spaces bareSortP {- PREDARGS tyVarIdP -}
--   where argP  = stringSymbol <$> argP'
--         argP' = try (lowerIdP <* colon) <|> positionNameP
        
-- bareSortP :: Parser BSort
-- bareSortP = toRSort <$> bareTypeP

xyP lP sepP rP
  = liftM3 (\x _ y -> (x, y)) lP (spaces >> sepP) rP

data ArrowSym = ArrowFun | ArrowPred

arrowP
  =   (reserved "->" >> return ArrowFun)
  <|> (reserved "=>" >> return ArrowPred)

positionNameP = dummyNamePos <$> getPosition
  
dummyNamePos pos  = "dummy." ++ name ++ ['.'] ++ line ++ ['.'] ++ col
    where name    = san <$> sourceName pos
          line    = show $ sourceLine pos  
          col     = show $ sourceColumn pos  
          san '/' = '.'
          san c   = toLower c

bareFunP  
  = do b  <- try bindP <|> dummyBindP 
       t1 <- bareArgP 
       a  <- arrowP
       t2 <- bareTypeP
       return $ bareArrow b t1 a t2 

dummyBindP 
  = stringSymbol <$> positionNameP -- (return dummyBind) -- (positionNameP)

bbindP = lowerIdP <* dcolon 

bindP  = liftM stringSymbol (lowerIdP <* colon)

dcolon = string "::" <* spaces

bareArrow b t1 ArrowFun t2
  = rFun b t1 t2
bareArrow _ t1 ArrowPred t2
  = foldr (rFun dummySymbol) t2 (getClasses t1)

-- isBoolBareType (RApp tc [] _ _) = tc == boolConName
-- isBoolBareType t                = False

isPropBareType (RApp tc [] _ _) = tc == propConName
-- isPropBareType t@(RApp _ [] _ _) = showPpr t == "(Prop)"
isPropBareType _                 = False


getClasses (RApp tc ts _ _) 
  | isTuple tc
  = getClass `fmap` ts 
getClasses t 
  = [getClass t]
getClass (RApp c ts _ _)
  = RCls c ts
getClass t
  = errorstar $ "Cannot convert " ++ (show t) ++ " to Class"

dummyP ::  Monad m => m (FReft -> b) -> m b
dummyP fm 
  = fm `ap` return dummyFReft 

refP :: Parser (t -> a) -> (Reft -> t)-> Parser a
refP kindP f
  = braces $ do
      v   <- symbolP 
      colon
      t   <- kindP
      reserved "|"
      ras <- refasP 
      return $ t (f (Reft (v, ras)))

symsP
  = do reserved "\\"
       ss <- sepBy symbolP spaces
       reserved "->"
       return ss

frefP :: Parser (FReft -> a) -> Parser a
frefP kindP
  = (try (do {ss <- symsP ; refP kindP (FSReft ss)}))
 <|> refP kindP FReft

predicatesP 
   =  try (angles $ sepBy1 predicate1P comma) 
  <|> return []

predicate1P 
   =  try (liftM RPoly (frefP bbaseP))
  <|> liftM (RMono . predUReft) monoPredicate1P

monoPredicateP 
   = try (angles monoPredicate1P) 
  <|> return pdTrue

monoPredicate1P
   =  try (reserved "True" >> return pdTrue)
  <|> try (liftM pdVar (parens predVarUseP))
  <|> liftM pdVar predVarUseP 

predVarUseP 
 = do p  <- predVarIdP
      xs <- sepBy exprP spaces
      return $ PV p dummyTyId [ (dummyTyId, dummySymbol, x) | x <- xs ]


------------------------------------------------------------------------
----------------------- Wrapped Constructors ---------------------------
------------------------------------------------------------------------

bRVar α p r               = RVar α (U r p)
bLst t rs r               = RApp listConName [t] rs (reftUReft r) 

bTup [t] _ r | isTauto r  = t
             | otherwise  = t `strengthen` (reftUReft r) 
bTup ts rs r              = RApp tupConName ts rs (reftUReft r)

bCon b [RMono r1] [] r    = RApp b [] [] (r1 `meet` (reftUReft r)) 
bCon b rs ts r            = RApp b ts rs (reftUReft r)

bAppTy v t r              = RAppTy (RVar v top) t (reftUReft r)




reftUReft      = (`U` pdTrue)
predUReft      = (U dummyFReft) 
dummyFReft      = FReft $ Reft (dummySymbol, [])
dummyTyId      = ""

------------------------------------------------------------------
--------------------------- Measures -----------------------------
------------------------------------------------------------------

data Pspec ty bndr 
  = Meas (Measure.Measure ty bndr) 
  | Assm (bndr, ty) 
  | Impt  Symbol
  | DDecl DataDecl
  | Incl  FilePath
  | Invt  ty
  | Alias (RTAlias String BareType)
  | PAlias (RTAlias Symbol Pred)
  | Embed (String, FTycon)

mkSpec name xs         = Measure.qualifySpec name $ Measure.Spec 
  { Measure.measures   = [m | Meas   m <- xs]
  , Measure.sigs       = [a | Assm   a <- xs]
  , Measure.invariants = [t | Invt   t <- xs] 
  , Measure.imports    = [i | Impt   i <- xs]
  , Measure.dataDecls  = [d | DDecl  d <- xs]
  , Measure.includes   = [q | Incl   q <- xs]
  , Measure.aliases    = [a | Alias  a <- xs]
  , Measure.paliases   = [p | PAlias p <- xs]
  , Measure.embeds     = M.fromList [e | Embed e <- xs]
  }

specificationP 
  = do reserved "module"
       reserved "spec"
       S name <- symbolP
       reserved "where"
       xs     <- grabs (specP <* whiteSpace) --(liftM2 const specP whiteSpace)
       return $ mkSpec name xs 


specP 
  = try (reserved "assume"    >> liftM Assm  tyBindP)
    <|> (reserved "assert"    >> liftM Assm  tyBindP)
    <|> (reserved "measure"   >> liftM Meas  measureP) 
    <|> (reserved "import"    >> liftM Impt  symbolP)
    <|> (reserved "data"      >> liftM DDecl dataDeclP)
    <|> (reserved "include"   >> liftM Incl  filePathP)
    <|> (reserved "invariant" >> liftM Invt  genBareTypeP)
    <|> (reserved "type"      >> liftM Alias aliasP)
    <|> (reserved "predicate" >> liftM PAlias paliasP)
    <|> (reserved "embed"     >> liftM Embed embedP)
    <|> ({- DEFAULT -}           liftM Assm  tyBindP)


filePathP :: Parser FilePath
filePathP = angles $ many1 pathCharP
  where pathCharP = choice $ char <$> pathChars 
        pathChars = ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ ['.', '/']

tyBindP 
  = xyP binderP dcolon genBareTypeP

genBareTypeP
  = bareTypeP -- liftM generalize bareTypeP 

embedP 
  = xyP upperIdP (reserved "as") fTyConP

aliasP  = rtAliasP id           bareTypeP
paliasP = rtAliasP stringSymbol predP

rtAliasP f bodyP
  = do name <- upperIdP
       spaces
       args <- sepBy aliasIdP spaces
       whiteSpace >> reservedOp "=" >> whiteSpace
       body <- bodyP 
       let (tArgs, vArgs) = partition (isLower . head) args
       return $ RTA name (f <$> tArgs) (f <$> vArgs) body

aliasIdP :: Parser String
aliasIdP = condIdP (['A' .. 'Z'] ++ ['a'..'z'] ++ ['0'..'9']) (isAlpha . head) 


measureP 
  = do (x, ty) <- tyBindP  
       whiteSpace
       eqns    <- grabs $ measureDefP $ (rawBodyP <|> tyBodyP ty)
       return   $ Measure.mkM x ty eqns   

rawBodyP 
  = braces $ do
      v <- symbolP 
      reserved "|"
      p <- predP
      return $ Measure.R v p

-- tyBodyP :: BareType -> Parser Measure.Body
tyBodyP ty 
  = case outTy ty of
      Just bt | isPropBareType bt -> Measure.P <$> predP 
      _                           -> Measure.E <$> exprP
    where outTy (RAllT _ t)    = outTy t
          outTy (RAllP _ t)    = outTy t
          outTy (RFun _ _ t _) = Just t
          outTy _              = Nothing

binderP :: Parser Symbol
binderP =  try $ liftM stringSymbol (idP badc)
       <|> liftM pwr (parens (idP bad))
       where idP p  = many1 (satisfy (not . p))
             badc c = (c == ':') ||  bad c
             bad c  = isSpace c || c `elem` "()"
             pwr s  = stringSymbol $ "(" ++ s ++ ")" 
             
grabs p = try (liftM2 (:) p (grabs p)) 
       <|> return []

measureDefP :: Parser Measure.Body -> Parser (Measure.Def Symbol)
measureDefP bodyP
  = do mname   <- symbolP
       (c, xs) <- parens $ measurePatP
       whiteSpace >> reservedOp "=" >> whiteSpace
       body    <- bodyP 
       whiteSpace
       return   $ Measure.Def mname (stringSymbol c) (stringSymbol <$> xs) body

measurePatP :: Parser (String, [String])
measurePatP
  =  try (liftM2 (,)   upperIdP (sepBy lowerIdP whiteSpace))
 <|> try (liftM3 (\x c y -> (c, [x,y])) lowerIdP colon lowerIdP)
 <|> (brackets whiteSpace  >> return ("[]",[])) 

{- len (Cons x1 x2 ...) = e -}


-------------------------------------------------------------------------------
--------------------------------- Predicates ----------------------------------
-------------------------------------------------------------------------------

dataConFieldsP 
  =   (braces $ sepBy predTypeDDP comma)
  <|> (sepBy (parens predTypeDDP) spaces)

predTypeDDP 
  = liftM2 (,) bbindP bareTypeP

dataConP
  = do x <- upperIdP
       spaces
       xts <- dataConFieldsP -- sepBy predTypeDDP spaces
       return (x, xts)



dataDeclP
  = do x   <- upperIdP
       spaces
       ts  <- sepBy tyVarIdP spaces
       ps  <- predVarDefsP
       whiteSpace >> reservedOp "=" >> whiteSpace
       dcs <- sepBy dataConP (reserved "|")
       whiteSpace
       -- spaces
       -- reservedOp "--"
       return $ D x ts ps dcs




instance Inputable BareType where
  rr' = doParse' bareTypeP 

instance Inputable (Measure.Measure BareType Symbol) where
  rr' = doParse' measureP

instance Inputable (Measure.Spec BareType Symbol) where
  rr' = doParse' specificationP

hsSpecificationP name 
  = doParse' $ liftM (mkSpec name) $ specWraps specP


grabUpto p  
  =  try (lookAhead p >>= return . Just)
 <|> try (eof         >> return Nothing)
 <|> (anyChar >> grabUpto p)

betweenMany leftP rightP p 
  = do z <- grabUpto leftP
       case z of
         Just _  -> liftM2 (:) (between leftP rightP p) (betweenMany leftP rightP p)
         Nothing -> return []

-- specWrap  = between     (string "{-@" >> spaces) (spaces >> string "@-}")
specWraps = betweenMany (string "{-@" >> spaces) (spaces >> string "@-}")

