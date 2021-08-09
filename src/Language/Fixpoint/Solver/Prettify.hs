{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

-- | Functions to make environments easier to read
module Language.Fixpoint.Solver.Prettify (savePrettifiedQuery) where

import           Data.Bifunctor (first)
import           Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import           Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import           Data.List (intersperse)
import           Language.Fixpoint.Misc (ensurePath)
import           Language.Fixpoint.Solver.EnvironmentReduction
  ( dropLikelyIrrelevantBindings
  , axiomEnvSymbols
  , inlineInSortedReft
  , mergeDuplicatedBindings
  , simplifyBooleanRefts
  , undoANF
  )
import           Language.Fixpoint.Types.Config (Config, queryFile)
import           Language.Fixpoint.Types.Constraints
import           Language.Fixpoint.Types.Environments
  (BindEnv, elemsIBindEnv, lookupBindEnv)
import           Language.Fixpoint.Types.Names (Symbol)
import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Refinements
  (SortedReft(..), conjuncts, reftBind, reftPred, sortedReftSymbols)
import           Language.Fixpoint.Types.Substitutions (exprSymbolsSet)
import qualified Language.Fixpoint.Utils.Files as Files
import           System.FilePath (addExtension)
import           Text.PrettyPrint.HughesPJ.Compat
  (Doc, braces, hang, nest, render, sep, text, vcat, (<+>), ($+$))


savePrettifiedQuery :: Fixpoint a => Config -> FInfo a -> IO ()
savePrettifiedQuery cfg fi = do
  let fq   = queryFile Files.Fq cfg `addExtension` "prettified"
  putStrLn $ "Saving prettified Query: "   ++ fq ++ "\n"
  ensurePath fq
  writeFile fq $ render (prettyConstraints fi)

prettyConstraints :: Fixpoint a => FInfo a -> Doc
prettyConstraints fi =
  vcat $ map (prettyConstraint aenvMap (bs fi)) $ HashMap.elems (cm fi)
  where
    aenvMap = axiomEnvSymbols (ae fi)

prettyConstraint
  :: Fixpoint a
  => HashMap Symbol (HashSet Symbol)
  -> BindEnv
  -> SubC a
  -> Doc
prettyConstraint aenv bindEnv c =
  let env = [ (s, ([bId], sr))
            | bId <- elemsIBindEnv $ senv c
            , let (s, sr) = lookupBindEnv bId bindEnv
            ]
      mergedEnv = mergeDuplicatedBindings env
      undoANFEnv = HashMap.union (undoANF 5 mergedEnv) mergedEnv
      boolSimplEnv = HashMap.union (simplifyBooleanRefts undoANFEnv) undoANFEnv

      simplifiedLhs = inlineInSortedReft 100 boolSimplEnv (slhs c)
      simplifiedRhs = inlineInSortedReft 100 boolSimplEnv (srhs c)
      prunedPrettyEnv =
        eraseUnusedBindings constraintSymbols $
        dropLikelyIrrelevantBindings aenv constraintSymbols $
        HashMap.map snd boolSimplEnv
      constraintSymbols =
        HashSet.union (sortedReftSymbols simplifiedLhs) (sortedReftSymbols simplifiedRhs)
   in hang (text "\n\nconstraint:") 2 $
          text "lhs" <+> toFix simplifiedLhs
      $+$ text "rhs" <+> toFix simplifiedRhs
      $+$ (pprId (sid c) <+> text "tag" <+> toFix (stag c))
      $+$ toFixMeta (text "simpleConstraint" <+> pprId (sid c)) (toFix (sinfo c))
      $+$ hang (text "environment:") 2
            (vcat $ intersperse "" $ elidedMessage : map prettyBind prunedPrettyEnv)
  where
    prettyBind (ms, sr) = sep [maybe "_" toFix ms <+> ":", nest 2 $ prettySortedRef sr]
    prettySortedRef sr = braces $ sep
      [ toFix (reftBind (sr_reft sr)) <+> ":" <+> toFix (sr_sort sr) <+> "|"
      , nest 2 $ toFix $ conjuncts $ reftPred $ sr_reft sr
      ]

    elidedMessage = "// elided some likely irrelevant bindings"

pprId :: Show a => Maybe a -> Doc
pprId (Just i)  = "id" <+> text (show i)
pprId _         = ""

toFixMeta :: Doc -> Doc -> Doc
toFixMeta k v = text "// META" <+> k <+> text ":" <+> v

-- | @eraseUnusedBindings ss env@ erases symbols that aren't refered from @ss@
-- or refinement types in the environment.
--
-- Erasure is accomplished by replacing the symbol with @Nothing@ in the
-- bindings.
eraseUnusedBindings
  :: HashSet Symbol -> HashMap Symbol SortedReft -> [(Maybe Symbol, SortedReft)]
eraseUnusedBindings ss env = map (first reachable) $ HashMap.toList env
  where
    allSymbols = HashSet.union ss envSymbols
    envSymbols =
      HashSet.unions $
      map (exprSymbolsSet . reftPred . sr_reft) $
      HashMap.elems env

    reachable s =
      if s `HashSet.member` allSymbols then
        Just s
      else
        Nothing
