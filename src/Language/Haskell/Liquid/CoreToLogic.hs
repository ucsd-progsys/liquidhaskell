{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-} 
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE TupleSections          #-}

module Language.Haskell.Liquid.CoreToLogic ( coreToDef , mkLit, runToLogic, LError(..) ) where

import GHC hiding (Located)
import Var

import qualified CoreSyn as C
import Literal
import IdInfo

import Control.Applicative 

import Language.Fixpoint.Misc
import Language.Fixpoint.Names (dropModuleNames, isPrefixOfSym)
import Language.Fixpoint.Types hiding (Def, R, simplify)
import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Types as F
import Language.Haskell.Liquid.GhcMisc hiding (isDictionary)
import Language.Haskell.Liquid.Types    hiding (GhcInfo(..), GhcSpec (..))


import qualified Data.HashMap.Strict as M

import Data.Monoid
import Data.Functor
import Data.Either

newtype LogicM a = LM (Either a LError)


data LError = LE String

instance Monad LogicM where
	return = LM . Left
	(LM (Left x))  >>= f = f x
	(LM (Right x)) >>= f = LM (Right x)

instance Functor LogicM where
	fmap f (LM (Left x))  = LM $ Left $ f x
	fmap f (LM (Right x)) = LM $ Right x

instance Applicative LogicM where
	pure = LM . Left

	(LM (Left f))  <*> (LM (Left x))  = LM $ Left (f x)
	(LM (Right f)) <*> (LM (Left x))  = LM $ Right f
	(LM (Left f))  <*> (LM (Right x)) = LM $ Right x
	(LM (Right f)) <*> (LM (Right x)) = LM $ Right x

throw :: String -> LogicM a
throw = LM . Right . LE

runToLogic (LM x) = x

coreToDef :: LocSymbol -> Var -> C.CoreExpr ->  LogicM [Def DataCon]
coreToDef x v e = go $ simplify e
  where
    go (C.Lam a e)  = go e
    go (C.Tick _ e) = go e
    go (C.Case _ _ _ alts) = mapM goalt alts
    go e'                 = throw "Measure Functions should have a case at top level"

    goalt ((C.DataAlt d), xs, e) = ((Def x d (symbol <$> xs)) . E) <$> coreToLogic e
    goalt alt = throw $ "Bad alternative" ++ showPpr alt


coreToLogic :: C.CoreExpr -> LogicM Expr
coreToLogic (C.Let b e)  = subst1 <$> coreToLogic e <*>  makesub b
coreToLogic (C.Tick _ e) = coreToLogic e
coreToLogic (C.App (C.Var v) e) | ignoreVar v = coreToLogic e
coreToLogic (C.Lit l)            
  = case mkLit l of 
     Nothing -> throw $ "Bad Literal in measure definition" ++ showPpr l
     Just i -> return i
coreToLogic (C.Var x)           = return $ EVar $ symbol x
coreToLogic e@(C.App _ _)       = toLogicApp e 
coreToLogic e                   = throw ("Cannot transform to Logic" ++ showPpr e)

toLogicApp :: C.CoreExpr -> LogicM Expr
toLogicApp e   
  =  do let (f, es) = splitArgs e
        args       <- reverse <$> (mapM coreToLogic es)
        (`makeApp` args) <$> tosymbol f

makeApp f [e1, e2] | Just op <- M.lookup (val f) bops
  = EBin op e1 e2

makeApp f args 
  = EApp f args

bops :: M.HashMap Symbol Bop
bops = M.fromList [ (symbol ("+" :: String), Plus)
                  , (symbol ("-" :: String), Minus)
                  , (symbol ("*" :: String), Times)
                  , (symbol ("/" :: String), Div)
                  , (symbol ("%" :: String), Mod)
                  ] 

splitArgs (C.App (C.Var i) e) | ignoreVar i       = splitArgs e
splitArgs (C.App f (C.Var v)) | isDictionary v    = splitArgs f
splitArgs (C.App f e) = (f', e:es) where (f', es) = splitArgs f
splitArgs f           = (f, [])

tosymbol (C.Var x) = return $ dummyLoc $ simpleSymbolVar x
tosymbol  e        = throw ("Bad Measure Definition:\n" ++ showPpr e ++ "\t cannot be applied")

makesub (C.NonRec x e) =  (symbol x,) <$> coreToLogic e
makesub  _             = throw "Cannot make Logical Substitution of Recursive Definitions"

mkLit :: Literal -> Maybe Expr
mkLit (MachInt    n)   = mkI n
mkLit (MachInt64  n)   = mkI n
mkLit (MachWord   n)   = mkI n
mkLit (MachWord64 n)   = mkI n
mkLit (MachFloat  n)   = mkR n
mkLit (MachDouble n)   = mkR n
mkLit (LitInteger n _) = mkI n
mkLit _                = Nothing -- ELit sym sort
mkI                    = Just . ECon . I  
mkR                    = Just . ECon . F.R . fromRational

ignoreVar i = simpleSymbolVar i `elem` ["I#"]


simpleSymbolVar  = dropModuleNames . symbol . showPpr . getName

isDictionary v   = isPrefixOfSym (symbol ("$" :: String)) (simpleSymbolVar v)

isDead = isDeadOcc . occInfo . idInfo

class Simplify a where
  simplify :: a -> a 

instance Simplify C.CoreExpr where
  simplify e@(C.Var x) 
    = e
  simplify e@(C.Lit _) 
    = e
  simplify (C.App e (C.Type _))                        
    = simplify e
  simplify (C.App e (C.Var dict))  | isDictionary dict 
    = simplify e
  simplify (C.App (C.Lam x e) _)   | isDead x          
    = simplify e
  simplify (C.App e1 e2) 
    = C.App (simplify e1) (simplify e2)
  simplify (C.Lam x e) | isTyVar x 
    = simplify e
  simplify (C.Lam x e) 
    = C.Lam x (simplify e)
  simplify (C.Let xes e) 
    = C.Let (simplify xes) (simplify e)
  simplify (C.Case e x t alts) 
    = C.Case (simplify e) x t (simplify <$> alts)
  simplify (C.Cast e c)    
    = simplify e
  simplify (C.Tick _ e) 
    = simplify e

instance Simplify C.CoreBind where
  simplify (C.NonRec x e) = C.NonRec x (simplify e)
  simplify (C.Rec xes)    = C.Rec (mapSnd simplify <$> xes )

instance Simplify C.CoreAlt where
  simplify (c, xs, e) = (c, xs, simplify e) 

