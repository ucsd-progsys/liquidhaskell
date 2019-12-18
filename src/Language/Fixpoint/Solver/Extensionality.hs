{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE PatternGuards        #-}
{-# LANGUAGE FlexibleContexts     #-}

module Language.Fixpoint.Solver.Extensionality (expand) where

import           Control.Monad.State
import qualified Data.HashMap.Strict       as M
import           Data.Maybe  (fromMaybe)
import qualified Data.List                 as L 

import           Language.Fixpoint.SortCheck
import           Language.Fixpoint.Types hiding (mapSort)
import           Language.Fixpoint.Types.Visitor ( (<$$>), mapSort )

expand :: SymEnv -> SInfo a -> SInfo a
expand senv si = evalState (expend si) $ initST senv (ddecls si)


class Expend a where
  expend :: a -> Ex a


instance Expend (SInfo a) where
  expend si = do 
    setBEnv (bs si)
    cm'      <- expend (cm si) 
    bs'      <- exbenv <$> get  
    return $ si{ cm = cm' , bs = bs' }

instance (Expend a) => Expend (M.HashMap SubcId a) where 
  expend h = M.fromList <$> mapM expend (M.toList h) 

instance (Expend a, Expend b) => Expend (a,b) where 
  expend (a,b) = (,) <$> expend a <*> expend b 

instance Expend SubcId where
  expend i = return i 

instance Expend (SimpC a) where
  expend c = do 
    setExBinds 
    rhs <- expend (_crhs c)
    is <- exbinds <$> get 
    return $ c{_crhs = rhs, _cenv = fromListIBindEnv is `unionIBindEnv` _cenv c}

instance Expend Expr where 
  expend e = mapMPosExpr Pos goP e >>= mapMPosExpr Pos goN 
    where  
      goP Pos (PAtom b e1 e2)
       | (b == Eq || b == Ne)
       , Just s <- bkFFunc (exprSort "extensionality" e1)
       = do let ss   = init $ snd s
            xs      <- mapM freshArg ss 
            env     <- exenv <$> get 
            let e1'  = eApps (unElab e1) xs 
            let e2'  = eApps (unElab e2) xs 
            let elab = elaborate (dummyLoc "extensionality") env
            return   $ PAtom b (elab e1') (elab e2')
      goP _ e = return e 
      goN Neg (PAtom b e1 e2)
       | (b == Eq || b == Ne)
       , Just s <- bkFFunc (exprSort "extensionality" e1)
       = do dds <- exddecl <$> get 
            let ss    = init $ snd s
            es       <- instantiate dds ss 
            env <- exenv <$> get 
            let e1' x = eApps (unElab e1) x 
            let e2' x = eApps (unElab e2) x 
            let elab  = elaborate (dummyLoc "extensionality") env
            let pAtom x = PAtom b (elab $ e1' x) (elab $ e2' x)
            return $ PAnd (pAtom <$> L.transpose es)
      goN _ e = return e 

instantiate :: [DataDecl]  -> [Sort] -> Ex [[Expr]]
instantiate ds ss = mapM instantiateOne (breakSort ds <$> ss)  

instantiateOne :: Either (LocSymbol, [Sort]) Sort  -> Ex [Expr]
instantiateOne (Right s@(FVar _)) = 
  (\x -> [EVar x]) <$> freshArgOne s
instantiateOne (Right s) = do 
  xss <- excbs <$> get 
  return [EVar x | (x,xs) <- xss, xs == s ] 
instantiateOne (Left (dc, ts)) = 
  (map (mkEApp dc) . combine) <$>  mapM instantiateOne (Right <$> ts) 

combine :: [[a]] -> [[a]]
combine []          = [[]]
combine ([]:_)      = []
combine ((x:xs):ys) = map (x:) (combine ys) ++ combine (xs:ys)


data Pos = Pos | Neg 
negatePos :: Pos -> Pos 
negatePos Pos = Neg 
negatePos Neg = Pos 

mapMPosExpr :: (Monad m) => Pos -> (Pos -> Expr -> m Expr) -> Expr -> m Expr
mapMPosExpr p f = go p 
  where
    go p e@(ESym _)      = f p e
    go p e@(ECon _)      = f p e
    go p e@(EVar _)      = f p e
    go p e@(PKVar _ _)   = f p e
    go p (PGrad k s i e) = f p =<< (PGrad k s i <$>  go p e                     )
    go p (ENeg e)        = f p =<< (ENeg        <$>  go p e                     )
    go p (PNot e)        = f p =<< (PNot        <$>  go p e                     )
    go p (ECst e t)      = f p =<< ((`ECst` t)  <$>  go p e                     )
    go p (PAll xts e)    = f p =<< (PAll   xts  <$>  go p e                     )
    go p (ELam (x,t) e)  = f p =<< (ELam (x,t)  <$>  go p e                     )
    go p (ECoerc a t e)  = f p =<< (ECoerc a t  <$>  go p e                     )
    go p (PExist xts e)  = f p =<< (PExist xts  <$>  go p e                     )
    go p (ETApp e s)     = f p =<< ((`ETApp` s) <$>  go p e                     )
    go p (ETAbs e s)     = f p =<< ((`ETAbs` s) <$>  go p e                     )
    go p (EApp g e)      = f p =<< (EApp        <$>  go p g  <*> go p e             )
    go p (EBin o e1 e2)  = f p =<< (EBin o      <$>  go p e1 <*> go p e2            )
    go p (PImp p1 p2)    = f p =<< (PImp        <$>  go (negatePos p) p1 <*> go p p2)
    go p (PIff p1 p2)    = f p =<< (PIff        <$>  go p p1 <*> go p p2            )
    go p (PAtom r e1 e2) = f p =<< (PAtom r     <$>  go p e1 <*> go p e2            )
    go p (EIte e e1 e2)  = f p =<< (EIte        <$>  go p e  <*> go p e1 <*> go p e2)
    go p (PAnd ps)       = f p =<< (PAnd        <$> (go p <$$> ps)                  )
    go p (POr  ps)       = f p =<< (POr         <$> (go p <$$> ps)                  )


type Ex    = State ExSt
data ExSt = ExSt { unique :: Int, exddecl :: [DataDecl] ,  exenv :: SymEnv, exbenv :: BindEnv, exbinds :: [BindId], excbs :: [(Symbol, Sort)] }

initST :: SymEnv -> [DataDecl]  -> ExSt
initST env dd = ExSt 0 (d:dd) env mempty mempty mempty
  where 
    -- NV: hardcore Haskell pairs because they do not appear in DataDecl (why?)
    d = tracepp "Tuple DataDecl" $ DDecl (symbolFTycon (dummyLoc tupConName)) 2 [ct]
    ct = DCtor (dummyLoc (symbol "GHC.Tuple.(,)")) [
            DField (dummyLoc (symbol "lqdc$select$GHC.Tuple.(,)$1")) (FVar 0)
          , DField (dummyLoc (symbol "lqdc$select$GHC.Tuple.(,)$2")) (FVar 1)
          ]


setBEnv :: BindEnv -> Ex () 
setBEnv benv = modify (\st -> st{exbenv = benv})

setExBinds :: Ex ()
setExBinds = modify (\st -> st{exbinds = []})

freshArg :: Sort -> Ex Expr 
freshArg s = do 
  st   <- get 
  case breakSort (exddecl st) s of 
    Left (dc, xs) -> do  
      xs <- mapM freshArgOne xs
      return $ mkEApp dc (EVar <$> xs)
    Right s -> EVar <$> freshArgOne s 


freshArgOne :: Sort -> Ex Symbol 
freshArgOne s = do 
  st   <- get 
  let x = symbol ("ext$" ++ show (unique st))
  let (id, benv') = insertBindEnv x (trueSortedReft s) (exbenv st)
  modify (\st -> st{exenv = insertSymEnv x s (exenv st), exbenv = benv', exbinds = id:exbinds st, unique = 1 + (unique st) , excbs = (x,s):(excbs st)})
  return x 


breakSort :: [DataDecl] -> Sort -> Either (LocSymbol, [Sort]) Sort 
breakSort ddecls s
    | Just (tc, ts) <- splitTC s
    , [([dd],i)] <- [ (ddCtors dd,ddVars dd) | dd <- ddecls, ddTyCon dd == tc ] 
    = Left (dcName dd, (instSort  (Sub $ zip [0..(i-1)] ts)) <$> dfSort <$> dcFields dd)
    | otherwise 
    = Right s

instSort :: Sub -> Sort -> Sort 
instSort (Sub su) x = mapSort go x 
  where 
    go :: Sort -> Sort 
    go (FVar i) = fromMaybe (FVar i) $ lookup i su  
    go s        = s 
  
splitTC :: Sort -> Maybe (FTycon, [Sort])
splitTC s 
     | (FTC f, ts) <- splitFApp s 
     = Just (f, ts)
     | otherwise
     = Nothing 

splitFApp :: Sort -> (Sort, [Sort])
splitFApp = go [] 
    where go acc (FApp s1 s2) = go (s2:acc) s1 
          go acc s            = (s, acc)