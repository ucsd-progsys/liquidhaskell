{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE ViewPatterns         #-}

module Test.Target.Targetable.Function () where

import           Control.Arrow                   (second)
import           Control.Monad
import qualified Control.Monad.Catch             as Ex
import           Control.Monad.Reader
import           Control.Monad.State
import           Data.Char
import qualified Data.HashMap.Strict             as M
import           Data.IORef
import           Data.Proxy
import qualified Data.Text                       as ST
import qualified Data.Text.Lazy.Builder          as Builder
import           System.IO.Unsafe

import qualified GHC
import           Language.Fixpoint.Smt.Interface -- hiding (SMTLIB2(..))
import           Language.Fixpoint.Types         hiding (ofReft, reft)
import           Language.Haskell.Liquid.GHC.Misc (qualifiedNameSymbol)
import           Language.Haskell.Liquid.Types.RefType (addTyConInfo, rTypeSort)
import           Language.Haskell.Liquid.Types   hiding (var)

import           Test.Target.Targetable
import           Test.Target.Eval
import           Test.Target.Expr
import           Test.Target.Monad
-- import           Test.Target.Serialize
import           Test.Target.Types
import           Test.Target.Util


getCtors :: SpecType -> [GHC.DataCon]
getCtors (RApp c _ _ _) = GHC.tyConDataCons $ rtc_tc c
getCtors (RAppTy t _ _) = getCtors t
getCtors (RFun _ i o _) = getCtors i ++ getCtors o
getCtors (RVar _ _)     = []
getCtors t              = error $ "getCtors: " ++ showpp t

dataConSymbol_noUnique :: GHC.DataCon -> Symbol
dataConSymbol_noUnique = qualifiedNameSymbol . GHC.getName

genFun :: Targetable a => Proxy a -> t -> Symbol -> SpecType -> Target Symbol
genFun _p _ x (stripQuals -> t)
  = do forM_ (getCtors t) $ \dc -> do
         let c = dataConSymbol_noUnique dc
         t <- lookupCtor c t
         addConstructor (c, rTypeSort mempty t)
       return x -- fresh (getType p)

stitchFun :: forall f. (Targetable (Res f))
          => Proxy f -> SpecType -> Target ([Expr] -> Res f)
stitchFun _ (bkArrowDeep . stripQuals -> (vs, tis, _, to))
  = do mref <- io $ newIORef []
       d <- asks depth
       state' <- get
       opts   <- ask
       let st = state' { variables = [], choices = [], constraints = []
                       , deps = mempty, constructors = [] }
       return $ \es -> unsafePerformIO $ runTarget opts st $ do
         -- let es = map toExpr xs
         mv <- lookup es <$> io (readIORef mref)
         case mv of
           Just v  -> return v
           Nothing -> do
             cts <- gets freesyms
             let env = map (second (`VC` [])) cts
             bs <- zipWithM (evalType (M.fromList env)) tis es
             case and bs of
               --FIXME: better error message
               False -> Ex.throwM $ PreconditionCheckFailed $ show $ zip es tis
               True  -> do
                 ctx  <- gets smtContext
                 let sEnv = ctxSymEnv ctx
                 _ <- io $ command ctx Push
                 xes <- zipWithM genExpr es tis
                 let su = mkSubst $ zipWith (\v e -> (v, var e)) vs xes
                 xo <- qquery (Proxy :: Proxy (Res f)) d (subst su to)
                 vs <- gets variables
                 mapM_ (\x -> io . smtWrite ctx . Builder.toLazyText $
                              smt2 sEnv $ makeDecl (seData sEnv) (symbol x) (snd x)) vs
                 cs <- gets constraints
                 mapM_ (\c -> io . smtWrite ctx . Builder.toLazyText $
                              smt2 sEnv $ Assert Nothing c) cs

                 resp <- io $ command ctx CheckSat
                 when (resp == Unsat) $ Ex.throwM SmtFailedToProduceOutput

                 o <- decode xo to
                 -- whenVerbose $ io $ printf "%s -> %s\n" (show es) (show o)
                 io (modifyIORef' mref ((es,o):))
                 _ <- io $ command ctx Pop
                 return o

genExpr :: Expr -> SpecType -> Target Symbol
genExpr (splitEApp_maybe -> Just (c, es)) t
  = do let ts = rt_args t
       xes <- zipWithM genExpr es ts
       (xs, _, _, to) <- bkArrowDeep . stripQuals <$> lookupCtor c t
       let su  = mkSubst $ zip xs $ map var xes
           to' = subst su to
       x <- fresh $ FObj $ symbol $ rtc_tc $ rt_tycon to'
       addConstraint $ ofReft (reft to') (var x)
       return x
genExpr (ECon (I i)) _t
  = do x <- fresh FInt
       addConstraint $ var x `eq` expr i
       return x
genExpr (ESym (SL s)) _t | ST.length s == 1
  -- This is a Char, so encode it as an Int
  = do x <- fresh FInt
       addConstraint $ var x `eq` expr (ord $ ST.head s)
       return x
genExpr e _t = error $ "genExpr: " ++ show e

evalType :: M.HashMap Symbol Val -> SpecType -> Expr -> Target Bool
evalType m t e@(splitEApp_maybe -> Just (c, xs))
  = do dcp <- lookupCtor c t
       tyi <- gets tyconInfo
       vts <- freshen $ applyPreds (addTyConInfo M.empty tyi t) dcp
       liftM2 (&&) (evalWith m (toReft $ rt_reft t) e) (evalTypes m vts xs)
evalType m t e
  = evalWith m (toReft $ rt_reft t) e

freshen :: [(Symbol, SpecType)] -> Target [(Symbol, SpecType)]
freshen [] = return []
freshen ((v,t):vts)
  = do n <- freshInt
       let v' = symbol . (++show n) . symbolString $ v
           su = mkSubst [(v,var v')]
           t' = subst su t
       vts' <- freshen $ subst su vts
       return ((v',t'):vts')

evalTypes
  :: M.HashMap Symbol Val
     -> [(Symbol, SpecType)] -> [Expr] -> Target Bool
evalTypes _ []         []     = return True
evalTypes m ((v,t):ts) (x:xs)
  = do xx <- evalExpr x m
       -- FIXME: tidy??
       let m' = M.insert (tidySymbol v) xx m
       liftM2 (&&) (evalType m' t x) (evalTypes m' ts xs)

evalTypes _ _ _ = error "evalTypes called with lists of unequal length!"

instance (Targetable a, Targetable b, b ~ Res (a -> b))
  => Targetable (a -> b) where
  getType _ = mkFFunc 0 [getType (Proxy :: Proxy a), getType (Proxy :: Proxy b)]
  query = genFun
  decode _ t
    = do f <- stitchFun (Proxy :: Proxy (a -> b)) t
         return $ \a -> f [toExpr a]
  toExpr  _ = var ("FUNCTION" :: Symbol)
  check _ _ = error "can't check a function!"

instance {-# OVERLAPPING #-} ( Targetable a, Targetable b, Targetable c
                             , c ~ Res (a -> b -> c)
                             ) => Targetable (a -> b -> c) where
  getType _ = mkFFunc 0 [getType (Proxy :: Proxy a), getType (Proxy :: Proxy b)
                        ,getType (Proxy :: Proxy c)]
  query = genFun
  decode _ t
    = do f <- stitchFun (Proxy :: Proxy (a -> b -> c)) t
         return $ \a b -> f [toExpr a, toExpr b]
  toExpr  _ = var ("FUNCTION" :: Symbol)
  check _ _ = error "can't check a function!"

instance {-# OVERLAPPING #-} ( Targetable a, Targetable b, Targetable c, Targetable d
                             , d ~ Res (a -> b -> c -> d)
                             ) => Targetable (a -> b -> c -> d) where
  getType _ = mkFFunc 0 [getType (Proxy :: Proxy a), getType (Proxy :: Proxy b)
                        ,getType (Proxy :: Proxy c), getType (Proxy :: Proxy d)]
  query = genFun
  decode _ t
    = do f <- stitchFun (Proxy :: Proxy (a -> b -> c -> d)) t
         return $ \a b c -> f [toExpr a, toExpr b, toExpr c]
  toExpr  _ = var ("FUNCTION" :: Symbol)
  check _ _ = error "can't check a function!"
