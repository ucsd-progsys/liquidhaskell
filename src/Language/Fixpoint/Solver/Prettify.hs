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
import           Data.List (intersperse, sortOn)
import           Data.Maybe (fromMaybe)
import           Data.Text (Text)
import qualified Data.Text as Text
import           Language.Fixpoint.Misc (ensurePath)
import           Language.Fixpoint.Solver.EnvironmentReduction
  ( dropLikelyIrrelevantBindings
  , inlineInSortedReft
  , mergeDuplicatedBindings
  , simplifyBooleanRefts
  , undoANF
  )
import           Language.Fixpoint.Types.Config (Config, queryFile)
import           Language.Fixpoint.Types.Constraints
import           Language.Fixpoint.Types.Environments
  (BindEnv, elemsIBindEnv, lookupBindEnv)
import           Language.Fixpoint.Types.Names
  ( Symbol
  , dropPrefixOfSym
  , prefixOfSym
  , suffixOfSym
  , suffixSymbol
  , symbol
  , symbolText
  )
import           Language.Fixpoint.Types.PrettyPrint
import           Language.Fixpoint.Types.Refinements
  ( Expr(..)
  , Reft
  , SortedReft(..)
  , conjuncts
  , reft
  , reftBind
  , reftPred
  , sortedReftSymbols
  , substf
  , substSortInExpr
  )
import           Language.Fixpoint.Types.Sorts (Sort(..), substSort)
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
  vcat $
  map (prettyConstraint (bs fi)) $
  map snd $
  sortOn fst $
  HashMap.toList (cm fi)

prettyConstraint
  :: Fixpoint a
  => BindEnv
  -> SubC a
  -> Doc
prettyConstraint bindEnv c =
  let env = [ (s, ([bId], sr))
            | bId <- elemsIBindEnv $ senv c
            , let (s, sr) = lookupBindEnv bId bindEnv
            ]
      mergedEnv = mergeDuplicatedBindings env
      undoANFEnv = HashMap.union (undoANF mergedEnv) mergedEnv
      boolSimplEnv = HashMap.union (simplifyBooleanRefts undoANFEnv) undoANFEnv

      simplifiedLhs = inlineInSortedReft boolSimplEnv (slhs c)
      simplifiedRhs = inlineInSortedReft boolSimplEnv (srhs c)

      prunedEnv =
        dropLikelyIrrelevantBindings (constraintSymbols simplifiedLhs simplifiedRhs) $
        HashMap.map snd boolSimplEnv
      (renamedEnv, c') =
        shortenVarNames prunedEnv c { slhs = simplifiedLhs, srhs = simplifiedRhs }
      prettyEnv =
        sortOn bindingSelector $
        eraseUnusedBindings (constraintSymbols (slhs c') (srhs c')) renamedEnv
   in hang (text "\n\nconstraint:") 2 $
          text "lhs" <+> toFix (slhs c')
      $+$ text "rhs" <+> toFix (srhs c')
      $+$ pprId (sid c) <+> text "tag" <+> toFix (stag c)
      $+$ toFixMeta (text "constraint" <+> pprId (sid c)) (toFix (sinfo c))
      $+$ hang (text "environment:") 2
            (vcat $ intersperse "" $ elidedMessage : map prettyBind prettyEnv)
  where
    prettyBind (s, sr) = sep [toFix s <+> ":", nest 2 $ prettySortedRef sr]
    prettySortedRef sr = braces $ sep
      [ toFix (reftBind (sr_reft sr)) <+> ":" <+> toFix (sr_sort sr) <+> "|"
      , nest 2 $ toFix $ conjuncts $ reftPred $ sr_reft sr
      ]

    elidedMessage = "// elided some likely irrelevant bindings"

    constraintSymbols sr0 sr1 =
      HashSet.union (sortedReftSymbols sr0) (sortedReftSymbols sr1)

    -- Sort by symbol then reft
    bindingSelector (s, sr) =
      ( -- put unused symbols at the end
        if "_" `Text.isPrefixOf` s then "{" <> s else s
      , reftBind (sr_reft sr)
      , sr_sort sr
      , reftPred $ sr_reft sr
      )

pprId :: Show a => Maybe a -> Doc
pprId (Just i)  = "id" <+> text (show i)
pprId _         = ""

toFixMeta :: Doc -> Doc -> Doc
toFixMeta k v = text "// META" <+> k <+> text ":" <+> v

-- | @eraseUnusedBindings ss env@ prefixes with @_@ the symbols that aren't
-- refered from @ss@ or refinement types in the environment.
eraseUnusedBindings
  :: HashSet Symbol -> [(Symbol, SortedReft)] -> [(Text, SortedReft)]
eraseUnusedBindings ss env = map (first reachable) env
  where
    allSymbols = HashSet.union ss envSymbols
    envSymbols =
      HashSet.unions $
      map (exprSymbolsSet . reftPred . sr_reft . snd) env

    reachable s =
      if s `HashSet.member` allSymbols then
        symbolText s
      else
        "_" <> symbolText s

-- | Shortens the names of refinements types in a given environment
-- and constraint
shortenVarNames
  :: HashMap Symbol SortedReft
  -> SubC a
  -> ([(Symbol, SortedReft)], SubC a)
shortenVarNames env c =
  let bindsRenameMap = proposeRenamings $ HashMap.keys env
      env' = map (renameBind bindsRenameMap) (HashMap.toList env)
   in
      (env', renameSubC bindsRenameMap c)
  where
    renameSubC :: HashMap Symbol Symbol -> SubC a -> SubC a
    renameSubC symMap c =
      mkSubC
        (senv c)
        (renameSortedReft symMap $ slhs c)
        (renameSortedReft symMap $ srhs c)
        (sid c)
        (stag c)
        (sinfo c)

    renameBind
      :: HashMap Symbol Symbol -> (Symbol, SortedReft) -> (Symbol, SortedReft)
    renameBind symMap (s, sr) =
      (at symMap s, renameSortedReft symMap sr)

    renameSortedReft
      :: HashMap Symbol Symbol -> SortedReft -> SortedReft
    renameSortedReft symMap (RR t r) =
      let sortSubst = FObj . (at symMap)
       in RR (substSort sortSubst t) (renameReft symMap r)

    renameReft :: HashMap Symbol Symbol -> Reft -> Reft
    renameReft symMap r =
      let m = HashMap.insert (reftBind r) (prefixOfSym $ reftBind r) symMap
          sortSubst = FObj . (at symMap)
       in reft (at m (reftBind r)) $
            substSortInExpr sortSubst $
            (substf (EVar . (at m)) $ reftPred r)

    at :: HashMap Symbol Symbol -> Symbol -> Symbol
    at m k = fromMaybe k $ HashMap.lookup k m

-- | Given a list of symbols with no duplicates, it proposes shorter
-- names to use for them.
--
-- All proposals preserve the prefix of the original name. A prefix is
-- the longest substring containing the initial character and no separator
-- ## ('symSepName').
--
-- Suffixes are preserved, except when symbols with a given prefix always
-- use the same suffix.
--
proposeRenamings :: [Symbol] -> HashMap Symbol Symbol
proposeRenamings = toSymMap . toPrefixSuffixMap

-- | Indexes symbols by prefix and then by suffix. If the prefix
-- equals the symbol, then the suffix is the empty symbol.
--
-- For instance,
--
-- > toPrefixSuffixMap ["a##b##c"] ! "a" ! "c" == ["a##b##c"]
-- > toPrefixSuffixMap ["a"] ! "a" ! "" == ["a"]
--
-- In general,
--
-- > forall ss.
-- > Set.fromList ss == Set.fromList $ concat [ xs | m <- elems (toPrefixSuffixMap ss), xs <- elems m ]
-- 
-- > forall ss.
-- > and [ all (pfx `isPrefixOfSym`) xs && all (sfx `isSuffixOfSym`) xs
-- >     | (pfx, m) <- toList (toPrefixSuffixMap ss)
-- >     , (sfx, xs) <- toList m
-- >     ]
--
-- TODO: put the above in unit tests
--
toPrefixSuffixMap :: [Symbol] -> HashMap Symbol (HashMap Symbol [Symbol])
toPrefixSuffixMap xs = HashMap.fromListWith (HashMap.unionWith (++))
  [ (pfx, HashMap.singleton sfx [s])
  | s <- xs
  , let pfx = prefixOfSym s
        sfx = suffixOfSym $ dropPrefixOfSym s
  ]

-- | Suggests renamings for every symbol in a given prefix/suffix map.
toSymMap :: HashMap Symbol (HashMap Symbol [Symbol]) -> HashMap Symbol Symbol
toSymMap prefixMap = HashMap.fromList
  [ r
  | (pfx, h) <- HashMap.toList prefixMap
  , r <- renameWithSuffixes pfx (HashMap.toList h)
  ]
  where
    renameWithSuffixes pfx = \case
      [(_sfx, ss)] -> renameWithAppendages pfx ("", ss)
      sfxs -> concatMap (renameWithAppendages pfx) sfxs

    renameWithAppendages pfx (sfx, ss) = zip ss $ case ss of
      [_s] -> [pfx `suffixIfNotNull` sfx]
      ss -> zipWith (rename pfx sfx) [1..] ss

    rename pfx sfx i _s =
      pfx `suffixIfNotNull` sfx `suffixSymbol` symbol (show i)

    suffixIfNotNull a b =
      if Text.null (symbolText b) then a else a `suffixSymbol` b
