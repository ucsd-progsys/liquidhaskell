{-# LANGUAGE DataKinds               #-}
{-# LANGUAGE UndecidableInstances    #-}
{-# LANGUAGE OverloadedStrings       #-}
{-# LANGUAGE RecordWildCards         #-}
{-# LANGUAGE BangPatterns            #-}
{-# LANGUAGE ConstraintKinds         #-}
{-# LANGUAGE DoAndIfThenElse         #-}
{-# LANGUAGE FlexibleContexts        #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE LambdaCase              #-}
{-# LANGUAGE ScopedTypeVariables     #-}
{-# LANGUAGE TypeFamilies            #-}
{-# LANGUAGE ViewPatterns            #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Test.Target.Testable (test, Testable, setup) where


import Prelude hiding (error, undefined)

import           Control.Exception               (AsyncException, evaluate)
import           Control.Monad
import           Control.Monad.Catch
import           Control.Monad.Reader
import           Control.Monad.State
-- import qualified Data.HashMap.Strict             as M
import qualified Data.HashSet                    as S
import qualified Data.List                       as L
import           Data.Proxy
import qualified Data.Text                       as ST
import qualified Data.Text.Lazy.Builder          as Builder
import           Data.Text.Format                hiding (print)
import           Data.Monoid
import           Text.Printf

import           Language.Fixpoint.Smt.Interface -- hiding (SMTLIB2(..))
import           Language.Fixpoint.Smt.Serialize (smt2SortMono)
-- import qualified Language.Fixpoint.Smt.Theories  as Thy
import           Language.Fixpoint.Types         hiding (Result)
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Types   hiding (env, var, Only)

import           Test.Target.Targetable          hiding (apply)
-- import           Test.Target.Eval
import           Test.Target.Expr
import           Test.Target.Monad
-- import           Test.Target.Serialize
import           Test.Target.Types
import           Test.Target.Util

import GHC.Err.Located

-- import Debug.Trace

-- | Test that a function inhabits the given refinement type by enumerating
-- valid inputs and calling the function on the inputs.
test :: Testable f => f -> SpecType -> Target Result
test f t
  = do d <- asks depth
       vs <- queryArgs f d t
       setup
       let (xs, tis, _, to) = bkArrowDeep $ stripQuals t
       ctx <- gets smtContext
       try (process f ctx vs (zip xs tis) to) >>= \case
         Left  (e :: TargetException) -> return $ Errored $ show e
         Right r                      -> return r

process :: Testable f
        => f -> Context -> [Symbol] -> [(Symbol,SpecType)] -> SpecType
        -> Target Result
process f ctx vs xts to = go 0 =<< io (command ctx CheckSat)
  where
    go !n Unsat    = return $ Passed n
    go _  (Error e)= throwM $ SmtError $ ST.unpack e
    go !n Sat      = do
      when (n `mod` 100 == 0) $ whenVerbose $ io $ printf "Checked %d inputs\n" n
      let n' = n + 1
      xs <- decodeArgs f vs (map snd xts)
      whenVerbose $ io $ print xs
      er <- io $ try $ evaluate (apply f xs)
      -- whenVerbose $ io $ print er
      case er of
        Left (e :: SomeException)
          -- DON'T catch AsyncExceptions since they are used by @timeout@
          | Just (_ :: AsyncException) <- fromException e -> throwM e
          | Just (SmtError _) <- fromException e -> throwM e
          | Just (ExpectedValues _) <- fromException e -> throwM e
          | otherwise -> do
              real <- gets realized
              modify $ \s@(TargetState {..}) -> s { realized = [] }
              let model = [ build "(= {} {})" (symbolText x, v) | (x,v) <- real ]
              unless (null model) $
                void $ io $ smtWrite ctx $ Builder.toLazyText
                          $ build "(assert (not (and {})))"
                     $ Only $ smt2many model
              mbKeepGoing xs n'
        Right r -> do
          real <- gets realized
          modify $ \s@(TargetState {..}) -> s { realized = [] }
          let su = mkSubst $ mkExprs f (map fst xts) xs
          (sat, _) <- check r (subst su to)

          -- refute model *after* checking output in case we have HOFs, which
          -- need to query the solver. if this is the last set of inputs, e.g.
          -- refuting the current model forces the solver to return unsat next
          -- time, the solver will return unsat when the HOF queries for an output,
          -- causing us to return a spurious error
          let model = [ build "(= {} {})" (symbolText x, v) | (x,v) <- real ]
          unless (null model) $
            void $ io $ smtWrite ctx $ Builder.toLazyText
                 $ build "(assert (not (and {})))"
                 $ Only $ smt2many model

          case sat of
            False -> mbKeepGoing xs n'
            True -> do
              asks maxSuccess >>= \case
                Nothing -> go n' =<< io (command ctx CheckSat)
                Just m | m == n' -> return $ Passed m
                       | otherwise -> go n' =<< io (command ctx CheckSat)

    go _ r = error $ "go _ " ++ show r

    mbKeepGoing xs n = do
      kg <- asks keepGoing
      if kg
        then go n =<< io (command ctx CheckSat)
        else return (Failed $ show xs)


{-# INLINE smt2many #-}
smt2many :: [Builder.Builder] -> Builder.Builder
smt2many []     = mempty
smt2many [b]    = b
smt2many (b:bs) = b <> mconcat [ " " <> b | b <- bs ]

-- | A class of functions that Target can test. A function is @Testable@ /iff/
-- all of its component types are 'Targetable' and all of its argument types are
-- 'Show'able.
--
-- You should __never__ have to define a new 'Testable' instance.
class (AllHave Targetable (Args f), Targetable (Res f)
      ,AllHave Show (Args f)) => Testable f where
  queryArgs  :: f -> Int -> SpecType -> Target [Symbol]
  decodeArgs :: f -> [Symbol] -> [SpecType] -> Target (HList (Args f))
  apply      :: f -> HList (Args f) -> Res f
  mkExprs    :: f -> [Symbol] -> HList (Args f) -> [(Symbol,Expr)]

instance {-# OVERLAPPING #-} (Show a, Targetable a, Testable b) => Testable (a -> b) where
  queryArgs f d (stripQuals -> (RFun x i o _))
    = do v  <- qquery (Proxy :: Proxy a) d i
         vs <- queryArgs (f undefined) d (subst (mkSubst [(x,var v)]) o)
         return (v:vs)
  queryArgs _ _ t = error $ "queryArgs called with non-function type: " ++ show t
  decodeArgs f (v:vs) (t:ts)
    = liftM2 (:::) (decode v t) (decodeArgs (f undefined) vs ts)
  decodeArgs _ _ _ = error "decodeArgs called with empty list"
  apply f (x ::: xs)
    = apply (f x) xs
  mkExprs f (v:vs) (x ::: xs)
    = (v, toExpr x) : mkExprs (f undefined) vs xs
  mkExprs _ _ _ = error "mkExprs called with empty list"

instance {-# OVERLAPPING #-}
  (Targetable a, Args a ~ '[], Res a ~ a) => Testable a
  where
  queryArgs _ _ _  = return []
  decodeArgs _ _ _ = return Nil
  apply f _        = f
  mkExprs _ _ _    = []

func :: Sort -> Bool
func (FAbs  _ s) = func s
func (FFunc _ _) = True
func _           = False

mySmt2Sort :: SymEnv -> Sort -> Builder.Builder
mySmt2Sort sEnv s = smt2SortMono s sEnv s

setup :: Target ()
setup = {-# SCC "setup" #-} do
   ctx  <- gets smtContext
   emb  <- gets embEnv
   let sEnv = ctxSymEnv ctx
    -- declare sorts
   ss  <- S.toList <$> gets sorts
   let defSort b e = io $ smtWrite ctx $ Builder.toLazyText
                   $ build "(define-sort {} () {})" (b,e)
   defSort ("CHOICE" :: Builder.Builder) ("Bool" :: Builder.Builder)
          -- FIXME: shouldn't need the nub, wtf?
   forM_ (L.nub (mySmt2Sort sEnv <$> ss)) $ \s ->
     defSort s ("Int" :: Builder.Builder)


   -- declare constructors
   cts <- gets constructors
   mapM_ (\ (c,t) -> do
             io $ smtWrite ctx . Builder.toLazyText $ smt2 sEnv $ makeDecl (seData sEnv) (symbol c) t) cts
   let nullary = [var c | (c,t) <- cts, not (func t)]
   unless (null nullary) $
     void $ io $ smtWrite ctx . Builder.toLazyText $ smt2 sEnv $ Distinct nullary
   -- declare variables
   vs <- gets variables
   let defVar (x,t) = io $ smtWrite ctx $ Builder.toLazyText $ smt2 sEnv $ makeDecl (seData sEnv) x (arrowize t)
   mapM_ defVar vs
   -- declare measures
   ms <- gets measEnv
   let defFun x t    = io $ smtWrite ctx $ Builder.toLazyText $ smt2 sEnv $ makeDecl (seData sEnv) x t
   forM_ ms $ \m -> do
     let x = val (name m)
     unless (x `memberSEnv` (seTheory sEnv)) $
       defFun x (rTypeSort emb (sort m))
   -- assert constraints
   cs <- gets constraints
   --mapM_ (\c -> do {i <- gets seed; modify $ \s@(GS {..}) -> s { seed = seed + 1 };
   --                 io . command ctx $ Assert (Just i) c})
   --  cs
   mapM_ (io . smtWrite ctx . Builder.toLazyText . smt2 sEnv . Assert Nothing) cs
   -- deps <- V.fromList . map (symbol *** symbol) <$> gets deps
   -- io $ generateDepGraph "deps" deps cs
   -- return (ctx,vs,deps)

-- sortTys :: Sort -> [Sort]
-- sortTys (FFunc _ ts) = concatMap sortTys ts
-- sortTys t            = [t]

arrowize :: Sort -> Sort
arrowize t
  | Just (_, ts, t) <- functionSort t
  = FObj . symbol . ST.intercalate "->" . map (symbolText . unObj) $ (ts ++ [t])
  | otherwise
  = t

unObj :: Sort -> Symbol
unObj FInt     = "Int"
unObj (FObj s) = s
unObj s        = error $ "unObj: " ++ show s
