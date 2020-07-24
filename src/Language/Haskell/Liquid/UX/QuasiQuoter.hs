{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TupleSections      #-}
{-# LANGUAGE OverloadedStrings  #-}

module Language.Haskell.Liquid.UX.QuasiQuoter 
-- (
--     -- * LiquidHaskell Specification QuasiQuoter
--     lq

--     -- * QuasiQuoter Annotations
--   , LiquidQuote(..)
--   ) 
  where

import SrcLoc (SrcSpan)

import Data.Data
import Data.List

import qualified Data.Text as T

import Language.Haskell.TH.Lib
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Quote

import Text.Parsec.Pos

import Language.Fixpoint.Types hiding (Error, Loc, SrcSpan)
import qualified Language.Fixpoint.Types as F

import Language.Haskell.Liquid.GHC.Misc (fSrcSpan)
import Language.Haskell.Liquid.Parse
import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.UX.Tidy

--------------------------------------------------------------------------------
-- LiquidHaskell Specification QuasiQuoter -------------------------------------
--------------------------------------------------------------------------------

lq :: QuasiQuoter
lq = QuasiQuoter
  { quoteExp  = bad
  , quotePat  = bad
  , quoteType = bad
  , quoteDec  = lqDec
  }
  where
    -- FIME(adinapoli) Should we preserve 'fail' here?
    bad = error "`lq` quasiquoter can only be used as a top-level declaration"

lqDec :: String -> Q [Dec]
lqDec src = do
  pos <- locSourcePos <$> location
  case singleSpecP pos src of
    Left err -> throwErrorInQ $ errorToUserError err
    Right spec -> do
      prg <- pragAnnD ModuleAnnotation $
               conE 'LiquidQuote `appE` dataToExpQ' spec
      case mkSpecDecs spec of
        Left err ->
          throwErrorInQ err
        Right decs ->
          return $ prg : decs

throwErrorInQ :: UserError -> Q a
throwErrorInQ err =
  fail . showpp =<< runIO (errorsWithContext [err])

--------------------------------------------------------------------------------
-- Liquid Haskell to Template Haskell ------------------------------------------
--------------------------------------------------------------------------------

-- Spec to Dec -----------------------------------------------------------------

mkSpecDecs :: BPspec -> Either UserError [Dec]
mkSpecDecs (Asrt (name, ty)) =
  return . SigD (symbolName name)
    <$> simplifyBareType name (quantifyFreeRTy $ val ty)
mkSpecDecs (LAsrt (name, ty)) =
  return . SigD (symbolName name)
    <$> simplifyBareType name (quantifyFreeRTy $ val ty)
mkSpecDecs (Asrts (names, (ty, _))) =
  (\t -> (`SigD` t) . symbolName <$> names)
    <$> simplifyBareType (head names) (quantifyFreeRTy $ val ty)
mkSpecDecs (Alias rta) =
  return . (TySynD name tvs) <$> simplifyBareType lsym (rtBody (val rta))
  where
    lsym = F.atLoc rta n 
    name = symbolName n 
    n    = rtName (val rta)
    tvs  = PlainTV . symbolName <$> rtTArgs (val rta)
mkSpecDecs _ =
  Right []

-- Symbol to TH Name -----------------------------------------------------------

symbolName :: Symbolic s => s -> Name
symbolName = mkName . symbolString . symbol

-- BareType to TH Type ---------------------------------------------------------

simplifyBareType :: LocSymbol -> BareType -> Either UserError Type
simplifyBareType s t = case simplifyBareType' t of
  Simplified t' ->
    Right t'
  FoundExprArg l ->
    Left $ ErrTySpec l Nothing (pprint $ val s) (pprint t) $ 
      "Found expression argument in bad location in type"
  FoundHole ->
    Left $ ErrTySpec (fSrcSpan s) Nothing (pprint $ val s) (pprint t) $ 
      "Can't write LiquidHaskell type with hole in a quasiquoter"

simplifyBareType' :: BareType -> Simpl Type
simplifyBareType' = simplifyBareType'' ([], [])

simplifyBareType'' :: ([BTyVar], [BareType]) -> BareType -> Simpl Type

simplifyBareType'' ([], []) (RVar v _) =
  return $ VarT $ symbolName v
simplifyBareType'' ([], []) (RAppTy t1 t2 _) =
  AppT <$> simplifyBareType' t1 <*> simplifyBareType' t2
simplifyBareType'' ([], []) (RFun _ i o _) =
  (\x y -> ArrowT `AppT` x `AppT` y)
    <$> simplifyBareType' i <*> simplifyBareType' o
simplifyBareType'' ([], []) (RApp cc as _ _) =
  let c  = btc_tc cc
      c' | isFun   c = ArrowT
         | isTuple c = TupleT (length as)
         | isList  c = ListT
         | otherwise = ConT $ symbolName c
  in  foldl' AppT c' <$> sequenceA (filterExprArgs $ simplifyBareType' <$> as)

simplifyBareType'' _ (RExprArg e) =
  FoundExprArg $ fSrcSpan e
simplifyBareType'' _ (RHole _) =
  FoundHole

simplifyBareType'' s(RAllP _ t) =
  simplifyBareType'' s t
simplifyBareType'' s (RAllE _ _ t) =
  simplifyBareType'' s t
simplifyBareType'' s (REx _ _ t) =
  simplifyBareType'' s t
simplifyBareType'' s (RRTy _ _ _ t) =
  simplifyBareType'' s t

simplifyBareType'' (tvs, cls) (RFun _ i o _)
  | isClassType i = simplifyBareType'' (tvs, i : cls) o
simplifyBareType'' (tvs, cls) (RAllT tv t _) =
  simplifyBareType'' (ty_var_value tv : tvs, cls) t

simplifyBareType'' (tvs, cls) t =
  ForallT (PlainTV . symbolName <$> reverse tvs)
    <$> mapM simplifyBareType' (reverse cls)
    <*> simplifyBareType' t


data Simpl a = Simplified a
             | FoundExprArg SrcSpan
             | FoundHole
               deriving (Functor)

instance Applicative Simpl where
  pure = Simplified

  Simplified   f <*> Simplified   x = Simplified $ f x
  _              <*> FoundExprArg l = FoundExprArg l
  _              <*> FoundHole      = FoundHole
  FoundExprArg l <*> _              = FoundExprArg l
  FoundHole      <*> _              = FoundHole

instance Monad Simpl where
  return = Simplified

  Simplified   x >>= f = f x
  FoundExprArg l >>= _ = FoundExprArg l
  FoundHole      >>= _ = FoundHole

filterExprArgs :: [Simpl a] -> [Simpl a]
filterExprArgs = filter check
  where
    check (FoundExprArg _) = False
    check _ = True

--------------------------------------------------------------------------------
-- QuasiQuoter Annotations -----------------------------------------------------
--------------------------------------------------------------------------------

newtype LiquidQuote = LiquidQuote { liquidQuoteSpec :: BPspec }
                      deriving (Data, Typeable)

--------------------------------------------------------------------------------
-- Template Haskell Utility Functions ------------------------------------------
--------------------------------------------------------------------------------

locSourcePos :: Loc -> SourcePos
locSourcePos loc =
  newPos (loc_filename loc) (fst $ loc_start loc) (snd $ loc_start loc)

dataToExpQ' :: Data a => a -> Q Exp
dataToExpQ' = dataToExpQ (const Nothing `extQ` textToExpQ)

textToExpQ :: T.Text -> Maybe ExpQ
textToExpQ text = Just $ varE 'T.pack `appE` stringE (T.unpack text)

extQ :: (Typeable a, Typeable b) => (a -> q) -> (b -> q) -> a -> q
extQ f g a = maybe (f a) g (cast a)

