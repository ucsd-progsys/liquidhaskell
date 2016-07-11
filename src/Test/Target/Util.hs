{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
module Test.Target.Util where


import           Control.Monad.IO.Class
import           Data.List
import           Data.Maybe

import           Data.Generics                   (everywhere, mkT)
import           Data.Text.Format                hiding (print)
import           Data.Text.Lazy.Builder          (Builder)
import           Debug.Trace

import qualified DynFlags as GHC
import qualified GhcMonad as GHC
import qualified GHC
import qualified GHC.Exts as GHC
import qualified GHC.Paths
import qualified HscTypes as GHC

-- import           Language.Fixpoint.Smt.Interface
-- import           Language.Fixpoint.Smt.Serialize


import           Language.Fixpoint.Types          hiding (prop)
import           Language.Haskell.Liquid.UX.CmdLine
import           Language.Haskell.Liquid.GHC.Interface
import           Language.Haskell.Liquid.Types.PredType
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Types    hiding (var)

import           Test.Target.Serialize


type Depth = Int

io ::  MonadIO m => IO a -> m a
io = liftIO

myTrace :: Show a => String -> a -> a
myTrace s x = trace (s ++ ": " ++ show x) x

reft :: SpecType -> Reft
reft = toReft . rt_reft

data HList (a :: [*]) where
  Nil   :: HList '[]
  (:::) :: a -> HList bs -> HList (a ': bs)

instance AllHave Show as => Show (HList as) where
  show Nil         = "()"
  show (x ::: Nil) = show x
  show (x ::: xs)  = show x ++ ", " ++ show xs

type family Map (f :: a -> b) (xs :: [a]) :: [b] where
  Map f '[]       = '[]
  Map f (x ': xs) = f x ': Map f xs

type family Constraints (cs :: [GHC.Constraint]) :: GHC.Constraint
type instance Constraints '[]       = ()
type instance Constraints (c ': cs) = (c, Constraints cs)

type AllHave (c :: k -> GHC.Constraint) (xs :: [k]) = Constraints (Map c xs)

type family Args a where
  Args (a -> b) = a ': Args b
  Args a        = '[]

type family Res a where
  Res (a -> b) = Res b
  Res a        = a

-- liquid-fixpoint started encoding `FObj s` as `Int` in 0.3.0.0, but we
-- want to preserve the type aliases for easier debugging.. so here's a
-- copy of the SMTLIB2 Sort instance..
-- smt2Sort :: Sort -> T.Text
-- smt2Sort s = case s of
--   FObj s' -> smt2 s'
--   _       -> smt2 s
-- smt2Sort s           | Just t <- Thy.smt2Sort s = t
-- smt2Sort FInt        = "Int"
-- smt2Sort (FApp t []) | t == intFTyCon = "Int"
-- smt2Sort (FApp t []) | t == boolFTyCon = "Bool"
-- --smt2Sort (FApp t [FApp ts _,_]) | t == appFTyCon  && fTyconSymbol ts == "Set_Set" = "Set"
-- smt2Sort (FObj s)    = smt2 s
-- smt2Sort s@(FFunc _ _) = error $ "smt2 FFunc: " ++ show s
-- smt2Sort _           = "Int"

makeDecl :: Symbol -> Sort -> Builder
-- FIXME: hack..
makeDecl x t
  | Just (_, ts, t) <- functionSort t
  = build "(declare-fun {} ({}) {})"
          (smt2 x, smt2s ts, smt2 t)
makeDecl x t
  = build "(declare-const {} {})" (smt2 x, smt2 t)

safeFromJust :: String -> Maybe a -> a
safeFromJust msg Nothing  = error $ "safeFromJust: " ++ msg
safeFromJust _   (Just x) = x

applyPreds :: SpecType -> SpecType -> [(Symbol,SpecType)]
applyPreds sp' dc = -- trace ("sp : " ++ showpp sp') $ trace ("dc : " ++ showpp dc)
                    zip xs (map tx ts)
  where
    sp = removePreds <$> sp'
    removePreds (MkUReft r _ _) = MkUReft r mempty mempty
    (as, ps, _, t) = bkUniv dc
    (xs, ts, _, _) = bkArrow . snd $ bkClass t
    -- args  = reverse tyArgs
    su    = [(ty_var_value tv, toRSort t, t) | tv <- as | t <- rt_args sp]
    sup   = [(p, r) | p <- ps | r <- rt_pargs sp]
    tx    = (\t -> replacePreds "applyPreds" t sup)
          . everywhere (mkT $ propPsToProp sup)
          . subsTyVars_meet su

propPsToProp :: [(RPVar, SpecProp)] -> SpecProp -> SpecProp
propPsToProp su r = foldr propPToProp r su

propPToProp :: (RPVar, SpecProp) -> SpecProp -> SpecProp
propPToProp (p, r) (RProp _ (RHole (MkUReft _ (Pr [up]) _)))
  | pname p == pname up
  = r
propPToProp _ m = m

splitEApp_maybe :: Expr -> Maybe (Symbol, [Expr])
splitEApp_maybe e@(EApp {}) = go [] e
  where
    go acc (EApp f e) = go (e:acc) f
    go acc (EVar s)   = Just (s, acc)
    go _   _          = Nothing -- error $ "splitEApp_maybe: " ++ showpp e
splitEApp_maybe _ = Nothing

stripQuals :: SpecType -> SpecType
stripQuals = snd . bkClass . fourth4 . bkUniv

fourth4 :: (t, t1, t2, t3) -> t3
fourth4 (_,_,_,d) = d

getSpec :: [String] -> FilePath -> IO GhcSpec
getSpec opts target
  = do cfg  <- getOpts ["--quiet"]
       spec.head.fst <$> getGhcInfo Nothing (cfg {ghcOptions = opts}) [target]
       -- case info of
       --   Left err -> error $ show err
       --   Right i  -> return $ spec i

runGhc :: [String] -> GHC.Ghc a -> IO a
runGhc o x = GHC.runGhc (Just GHC.Paths.libdir) $ do
               df <- GHC.getSessionDynFlags
               let df' = df { GHC.ghcMode   = GHC.CompManager
                            , GHC.ghcLink   = GHC.NoLink --GHC.LinkInMemory
                            , GHC.hscTarget = GHC.HscNothing --GHC.HscInterpreted
                            -- , GHC.optLevel  = 0 --2
                            , GHC.log_action = \_ _ _ _ _ -> return ()
                            } `GHC.gopt_set` GHC.Opt_ImplicitImportQualified
                              `GHC.xopt_set` GHC.Opt_MagicHash
               (df'',_,_) <- GHC.parseDynamicFlags df' (map GHC.noLoc o)
               _ <- GHC.setSessionDynFlags df''
               x

loadModule :: FilePath -> GHC.Ghc GHC.ModSummary
loadModule f = do target <- GHC.guessTarget f Nothing
                  --lcheck <- GHC.guessTarget "src/Test/Target.hs" Nothing
                  GHC.setTargets [target] -- [target,lcheck]
                  _ <- GHC.load GHC.LoadAllTargets
                  modGraph <- GHC.getModuleGraph
                  let m = fromJust $ find ((==f) . GHC.msHsFilePath) modGraph
                  GHC.setContext [ GHC.IIModule (GHC.ms_mod_name m)
                                 --, GHC.IIDecl $ GHC.simpleImportDecl
                                 --             $ GHC.mkModuleName "Test.Target"
                                 ]
                  return m
