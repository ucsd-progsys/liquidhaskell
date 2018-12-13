{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ParallelListComp  #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE BangPatterns      #-}

module Language.Haskell.Liquid.Bare.Class 
  ( makeClasses
  , makeSpecDictionaries
  , makeDefaultMethods
  ) 
  where

import           Data.Bifunctor 
import qualified Data.Maybe                                 as Mb
import qualified Data.HashMap.Strict                        as M

import qualified Language.Fixpoint.Misc                     as Misc
import qualified Language.Fixpoint.Types                    as F

import           Language.Haskell.Liquid.Types.Dictionaries
import qualified Language.Haskell.Liquid.GHC.Misc           as GM
import qualified Language.Haskell.Liquid.GHC.API            as Ghc
import           Language.Haskell.Liquid.Misc
import           Language.Haskell.Liquid.Types.RefType
import           Language.Haskell.Liquid.Types              hiding (freeTyVars)

import qualified Language.Haskell.Liquid.Measure            as Ms
import           Language.Haskell.Liquid.Bare.Types         as Bare 
import           Language.Haskell.Liquid.Bare.Resolve       as Bare
import           Language.Haskell.Liquid.Bare.Expand        as Bare

-------------------------------------------------------------------------------
makeClasses :: Bare.Env -> Bare.SigEnv -> ModName -> Bare.ModSpecs 
            -> ([DataConP], [(ModName, Ghc.Var, LocSpecType)])
-------------------------------------------------------------------------------
makeClasses env sigEnv myName specs = 
  second mconcat . unzip 
  $ [ cls | (name, spec) <- M.toList specs
          , cls          <- Ms.classes spec
          , tc           <- Mb.maybeToList (classTc cls) 
          , cls          <- Mb.maybeToList (mkClass env sigEnv myName name cls tc)
    ]
  where
    classTc = Bare.maybeResolveSym env myName "makeClass" . btc_tc . rcName 

mkClass :: Bare.Env -> Bare.SigEnv -> ModName -> ModName -> RClass LocBareType -> Ghc.TyCon 
        -> Maybe (DataConP, [(ModName, Ghc.Var, LocSpecType)])
mkClass env sigEnv _myName name (RClass cc ss as ms) 
  = Bare.failMaybe env name 
  . mkClassE env sigEnv _myName name (RClass cc ss as ms) 

mkClassE :: Bare.Env -> Bare.SigEnv -> ModName -> ModName -> RClass LocBareType -> Ghc.TyCon 
         -> Either UserError (DataConP, [(ModName, Ghc.Var, LocSpecType)])
mkClassE env sigEnv _myName name (RClass cc ss as ms) tc = do 
    ss'    <- mapM (mkConstr   env sigEnv name) ss 
    meths  <- mapM (makeMethod env sigEnv name) ms'
    let vts = [ (m, v, t) | (m, kv, t) <- meths, v <- Mb.maybeToList (plugSrc kv) ]
    let sts = [(val s, unClass $ val t) | (s, _) <- ms | (_, _, t) <- meths]
    let dcp = DataConP l dc αs [] [] (val <$> ss') (reverse sts) t False (F.symbol name) l'
    return  $ F.notracepp msg (dcp, vts)
  where
    c      = btc_tc cc
    l      = loc  c
    l'     = locE c
    msg    = "MKCLASS: " ++ F.showpp (cc, as, αs) 
    (dc:_) = Ghc.tyConDataCons tc
    αs     = bareRTyVar <$> as
    as'    = [rVar $ GM.symbolTyVar $ F.symbol a | a <- as ]
    ms'    = [ (s, rFun "" (RApp cc (flip RVar mempty <$> as) [] mempty) <$> t) | (s, t) <- ms]
    t      = rCls tc as'

mkConstr :: Bare.Env -> Bare.SigEnv -> ModName -> LocBareType -> Either UserError LocSpecType     
mkConstr env sigEnv name = fmap (fmap dropUniv) . Bare.cookSpecTypeE env sigEnv name Bare.GenTV 
  where 
    dropUniv t           = t' where (_, _, _, t') = bkUniv t

   --FIXME: cleanup this code
unClass :: SpecType -> SpecType 
unClass = snd . bkClass . fourth4 . bkUniv

makeMethod :: Bare.Env -> Bare.SigEnv -> ModName -> (LocSymbol, LocBareType) 
         -> Either UserError (ModName, PlugTV Ghc.Var, LocSpecType)
makeMethod env sigEnv name (lx, bt) = (name, mbV,) <$> Bare.cookSpecTypeE env sigEnv name mbV bt
  where 
    mbV = case Bare.maybeResolveSym env name "makeMethod" lx of 
            Just v  -> Bare.LqTV v 
            Nothing -> Bare.GenTV 

-------------------------------------------------------------------------------
makeSpecDictionaries :: Bare.Env -> Bare.SigEnv -> ModSpecs -> DEnv Ghc.Var SpecType 
-------------------------------------------------------------------------------
makeSpecDictionaries env sigEnv specs
  = dfromList 
  . concat 
  . fmap (makeSpecDictionary env sigEnv) 
  $ M.toList specs

makeSpecDictionary :: Bare.Env -> Bare.SigEnv -> (ModName, Ms.BareSpec)
                   -> [(Ghc.Var, M.HashMap F.Symbol (RISig SpecType))]
makeSpecDictionary env sigEnv (name, spec)
  = Mb.catMaybes 
  . resolveDictionaries env name 
  . fmap (makeSpecDictionaryOne env sigEnv name) 
  . Ms.rinstance 
  $ spec

makeSpecDictionaryOne :: Bare.Env -> Bare.SigEnv -> ModName 
                      -> RInstance LocBareType 
                      -> (F.Symbol, M.HashMap F.Symbol (RISig SpecType))
makeSpecDictionaryOne env sigEnv name (RI x t xts)
         = makeDictionary $ RI x (val . mkTy <$> t) [(x, mkLSpecIType t) | (x, t) <- xts ] 
  where
    mkTy :: LocBareType -> LocSpecType
    mkTy = Bare.cookSpecType env sigEnv name Bare.GenTV 

    mkLSpecIType :: RISig LocBareType -> RISig SpecType
    mkLSpecIType = fmap (val . mkTy)

resolveDictionaries :: Bare.Env -> ModName -> [(F.Symbol, M.HashMap F.Symbol (RISig SpecType))] 
                    -> [Maybe (Ghc.Var, M.HashMap F.Symbol (RISig SpecType))]
resolveDictionaries env name = fmap lookupVar 
                             . concat 
                             . fmap addInstIndex 
                             . Misc.groupList 
  where
    lookupVar (x, inst)      = (, inst) <$> Bare.maybeResolveSym env name "resolveDict" (F.dummyLoc x)

-- formerly, addIndex
-- GHC internal postfixed same name dictionaries with ints
addInstIndex            :: (F.Symbol, [a]) -> [(F.Symbol, a)]
addInstIndex (x, is) = go 0 (reverse is)
  where 
    go _ []          = []
    go _ [i]         = [(x, i)]
    go j (i:is)      = (F.symbol (F.symbolString x ++ show j),i) : go (j+1) is

----------------------------------------------------------------------------------
makeDefaultMethods :: Bare.Env -> [(ModName, Ghc.Var, LocSpecType)] 
                   -> [(ModName, Ghc.Var, LocSpecType)]
----------------------------------------------------------------------------------
makeDefaultMethods env mts = [ (mname, dm, t) 
                                 | (mname, m, t) <- mts
                                 , dm            <- lookupDefaultVar env mname m ]  

lookupDefaultVar :: Bare.Env -> ModName -> Ghc.Var -> [Ghc.Var] 
lookupDefaultVar env name v = Mb.maybeToList 
                            . Bare.maybeResolveSym env name "default-method" 
                            $ dmSym
  where 
    dmSym                   = F.atLoc v (GM.qualifySymbol mSym dnSym)
    dnSym                   = F.mappendSym "$dm" nSym
    (mSym, nSym)            = GM.splitModuleName (F.symbol v) 