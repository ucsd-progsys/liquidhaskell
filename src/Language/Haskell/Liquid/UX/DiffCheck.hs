-- | This module contains the code for Incremental checking, which finds the
--   part of a target file (the subset of the @[CoreBind]@ that have been
--   modified since it was last checked, as determined by a diff against
--   a saved version of the file.

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections     #-}

{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Language.Haskell.Liquid.UX.DiffCheck (

   -- * Changed binders + Unchanged Errors
     DiffCheck (..)

   -- * Use previously saved info to generate DiffCheck target
   , slice

   -- * Use target binders to generate DiffCheck target
   , thin -- , ThinDeps (..)

   -- * Save current information for next time
   , saveResult

   -- * Names of top-level binders that are rechecked
   , checkedVars

   -- * CoreBinds defining given set of Var
   , filterBinds
   , coreDeps
   , dependsOn
   , Def(..)
   , coreDefs
   )
   where


import           Prelude                                hiding (error)
import           Data.Aeson
import qualified Data.Text                              as T
import           Data.Algorithm.Diff
import           Data.Maybe                             (maybeToList, listToMaybe, mapMaybe, fromMaybe)
import qualified Data.IntervalMap.FingerTree            as IM
import qualified Data.HashSet                           as S
import qualified Data.HashMap.Strict                    as M
import qualified Data.List                              as L
import           System.Directory                       (copyFile, doesFileExist)
import           Language.Fixpoint.Types                (atLoc, FixResult (..), SourcePos(..), safeSourcePos, unPos)
-- import qualified Language.Fixpoint.Misc                 as Misc
import           Language.Fixpoint.Utils.Files
import           Language.Fixpoint.Solver.Stats ()
import           Language.Haskell.Liquid.Misc           (mkGraph)
import           Liquid.GHC.Misc
import           Liquid.GHC.API        as Ghc hiding ( Located
                                                                      , sourceName
                                                                      , text
                                                                      , panic
                                                                      , showPpr
                                                                      )
import           Text.PrettyPrint.HughesPJ              (text, render, Doc)
import qualified Data.ByteString                        as B
import qualified Data.ByteString.Lazy                   as LB

import           Language.Haskell.Liquid.Types          hiding (Def, LMap)

--------------------------------------------------------------------------------
-- | Data Types ----------------------------------------------------------------
--------------------------------------------------------------------------------

-- | Main type of value returned for diff-check.
data DiffCheck = DC
  { newBinds  :: [CoreBind]
  , oldOutput :: !(Output Doc)
  , newSpec   :: !TargetSpec
  }

instance PPrint DiffCheck where
  pprintTidy k dc = pprintTidy k (checkedVars dc) <> pprintTidy k (oldOutput dc)


-- | Variable definitions
data Def  = D
  { start  :: Int -- ^ line at which binder definition starts
  , end    :: Int -- ^ line at which binder definition ends
  , binder :: Var -- ^ name of binder
  }
  deriving (Eq, Ord)

-- | Variable dependencies "call-graph"
type Deps = M.HashMap Var (S.HashSet Var)

-- | Map from saved-line-num ---> current-line-num
type LMap   = IM.IntervalMap Int Int

-- | Intervals of line numbers that have been re-checked
type ChkItv = IM.IntervalMap Int ()

instance Show Def where
  show (D i j x) = showPpr x ++ " start: " ++ show i ++ " end: " ++ show j

--------------------------------------------------------------------------------
-- | `checkedNames` returns the names of the top-level binders that will be checked
--------------------------------------------------------------------------------
checkedVars              ::  DiffCheck -> [Var]
checkedVars              = concatMap names . newBinds
   where
     names (NonRec v _ ) = [v]
     names (Rec xs)      = fst <$> xs

--------------------------------------------------------------------------------
-- | `slice` returns a subset of the @[CoreBind]@ of the input `target`
--    file which correspond to top-level binders whose code has changed
--    and their transitive dependencies.
--------------------------------------------------------------------------------
slice :: FilePath -> [CoreBind] -> TargetSpec -> IO (Maybe DiffCheck)
--------------------------------------------------------------------------------
slice target cbs sp = do
  ex <- doesFileExist savedFile
  if ex
    then doDiffCheck
    else return Nothing
  where
    savedFile       = extFileName Saved target
    doDiffCheck     = sliceSaved target savedFile cbs sp

sliceSaved :: FilePath -> FilePath -> [CoreBind] -> TargetSpec -> IO (Maybe DiffCheck)
sliceSaved target savedFile coreBinds spec = do
  (is, lm) <- lineDiff target savedFile
  result   <- loadResult target
  return    $ sliceSaved' target is lm (DC coreBinds result spec)

sliceSaved' :: FilePath -> [Int] -> LMap -> DiffCheck -> Maybe DiffCheck
sliceSaved' srcF is lm (DC coreBinds result spec)
  | gDiff     = Nothing
  | otherwise = Just $ DC cbs' res' sp'
  where
    gDiff     = globalDiff srcF is spec
    sp'       = assumeSpec sigm spec
    res'      = adjustOutput lm cm result
    cm        = checkedItv (coreDefs cbs')
    cbs'      = thinWith sigs coreBinds (diffVars is defs)
    defs      = coreDefs coreBinds ++ specDefs srcF spec
    sigs      = S.fromList $ M.keys sigm
    sigm      = sigVars srcF is spec

-- | Add the specified signatures for vars-with-preserved-sigs,
--   whose bodies have been pruned from [CoreBind] into the "assumes"

assumeSpec :: M.HashMap Var LocSpecType -> TargetSpec -> TargetSpec
assumeSpec sigm sp = sp { gsSig = gsig { gsAsmSigs = M.toList $ M.union sigm assm } }
  where
    assm           = M.fromList (gsAsmSigs gsig)
    gsig           = gsSig sp

diffVars :: [Int] -> [Def] -> [Var]
diffVars ls defs'    = -- tracePpr ("INCCHECK: diffVars lines = " ++ show ls ++ " defs= " ++ show defs) $
                         go (L.sort ls) defs
  where
    defs             = L.sort defs'
    go _      []     = []
    go []     _      = []
    go (i:is) (d:ds)
      | i < start d  = go is (d:ds)
      | i > end d    = go (i:is) ds
      | otherwise    = binder d : go (i:is) ds

sigVars :: FilePath -> [Int] -> TargetSpec -> M.HashMap Var LocSpecType
sigVars srcF ls sp = M.fromList $ filter (ok . snd) $ specSigs sp
  where
    ok             = not . isDiff srcF ls

globalDiff :: FilePath -> [Int] -> TargetSpec -> Bool
globalDiff srcF ls gspec = measDiff || invsDiff || dconsDiff
  where
    measDiff  = any (isDiff srcF ls) (snd <$> gsMeas spec)
    invsDiff  = any (isDiff srcF ls) (snd <$> gsInvariants spec)
    dconsDiff = any (isDiff srcF ls) [ atLoc ldc () | ldc <- gsDconsP (gsName gspec) ]
    spec      = gsData gspec

isDiff :: FilePath -> [Int] -> Located a -> Bool
isDiff srcF ls x = file x == srcF && any hits ls
  where
    hits i       = line x <= i && i <= lineE x

--------------------------------------------------------------------------------
-- | @thin cbs sp vs@ returns a subset of the @cbs :: [CoreBind]@ which
--   correspond to the definitions of @vs@ and the functions transitively
--   called therein for which there are *no* type signatures. Callees with
--   type signatures are assumed to satisfy those signatures.
--------------------------------------------------------------------------------

{- data ThinDeps = Trans [Var] -- ^ Check all transitive dependencies
              | None   Var  -- ^ Check only the given binders
 -}

--------------------------------------------------------------------------------
thin :: [CoreBind] -> TargetSpec -> [Var] -> DiffCheck
--------------------------------------------------------------------------------
-- thin cbs sp (Trans vs) = DC (thinWith S.empty cbs vs ) mempty sp
thin cbs sp vs = DC (filterBinds      cbs vs') mempty sp'
  where
    vs'        = txClosure (coreDeps cbs) xs (S.fromList vs)
    sp'        = assumeSpec sigs' sp
    sigs'      = foldr M.delete (M.fromList xts) vs
    xts        = specSigs sp
    xs         = S.fromList $ fst <$> xts

thinWith :: S.HashSet Var -> [CoreBind] -> [Var] -> [CoreBind]
thinWith sigs cbs xs = filterBinds cbs calls
  where
    calls    = txClosure cbDeps sigs (S.fromList xs)
    cbDeps   = coreDeps cbs

coreDeps    :: [CoreBind] -> Deps
coreDeps bs = mkGraph $ calls ++ calls'
  where
    calls   = concatMap deps bs
    calls'  = [(y, x) | (x, y) <- calls]
    deps b  = [(x, y) | x <- bindersOf b
                      , y <- freeVars S.empty b
                      , S.member y defVars
              ]
    defVars = S.fromList (letVars bs)

-- | Given a call graph, and a list of vars, `dependsOn`
--   checks all functions to see if they call any of the
--   functions in the vars list.
--   If any do, then they must also be rechecked.

dependsOn :: Deps -> [Var] -> S.HashSet Var
dependsOn cg vars  = S.fromList results
  where
    preds          = map S.member vars
    filteredMaps   = M.filter <$> preds <*> pure cg
    results        = map fst $ M.toList $ M.unions filteredMaps

txClosure :: Deps -> S.HashSet Var -> S.HashSet Var -> S.HashSet Var
txClosure d sigs    = go S.empty
  where
    next            = S.unions . fmap deps . S.toList
    deps x          = M.lookupDefault S.empty x d
    go seen new
      | S.null new  = seen
      | otherwise   = let seen' = S.union seen new
                          new'  = next new `S.difference` seen'
                          new'' = new'     `S.difference` sigs
                      in go seen' new''



--------------------------------------------------------------------------------
filterBinds        :: [CoreBind] -> S.HashSet Var -> [CoreBind]
--------------------------------------------------------------------------------
filterBinds cbs ys = filter f cbs
  where
    f (NonRec x _) = x `S.member` ys
    f (Rec xes)    = any (`S.member` ys) $ fst <$> xes


--------------------------------------------------------------------------------
specDefs :: FilePath -> TargetSpec -> [Def]
--------------------------------------------------------------------------------
specDefs srcF  = map def . filter sameFile . specSigs
  where
    def (x, t) = D (line t) (lineE t) x
    sameFile   = (srcF ==) . file . snd

specSigs :: TargetSpec -> [(Var, LocSpecType)]
specSigs sp = gsTySigs  (gsSig  sp)
           ++ gsAsmSigs (gsSig  sp)
           ++ gsCtors   (gsData sp)

instance PPrint Def where
  pprintTidy _ d = text (show d)


--------------------------------------------------------------------------------
coreDefs     :: [CoreBind] -> [Def]
--------------------------------------------------------------------------------
coreDefs cbs = coreExprDefs xm xes
  where
    xes      = coreVarExprs cbs
    xm       = varBounds xes

coreExprDefs :: M.HashMap Var (Int, Int) -> [(Var, CoreExpr)]-> [Def]
coreExprDefs xm xes =
  L.sort
    [ D l l' x
      | (x, e) <- xes
      , (l, l') <- maybeToList $ coreExprDef xm (x, e)
    ]

coreExprDef :: M.HashMap Var (Int, Int) -> (Var, CoreExpr) -> Maybe (Int, Int)
coreExprDef m (x, e) = meetSpans eSp vSp
  where
    eSp              = lineSpan x $ catSpans x $ exprSpans e
    vSp              = M.lookup x m
    -- vSp   = lineSpan x (getSrcSpan x)

coreVarExprs :: [CoreBind] -> [(Var, CoreExpr)]
coreVarExprs = filter ok . concatMap varExprs
  where
    ok       = isGoodSrcSpan . getSrcSpan . fst

varExprs :: Bind a -> [(a, Expr a)]
varExprs (NonRec x e) = [(x, e)]
varExprs (Rec xes)    = xes

-- | varBounds computes upper and lower bounds on where each top-level binder's
--   definition can be by using ONLY the lines where the binder is defined.
varBounds :: [(Var, CoreExpr)] -> M.HashMap Var (Int, Int)
varBounds = M.fromList . defBounds . varDefs

varDefs :: [(Var, CoreExpr)] -> [(Int, Var)]
varDefs xes =
  L.sort [ (l, x) | (x,_) <- xes, let Just (l, _) = lineSpan x (getSrcSpan x) ]

defBounds :: [(Int, Var)] -> [(Var, (Int, Int) )]
defBounds ((l, x) : lxs@((l', _) : _ )) = (x, (l, l' - 1)) : defBounds lxs
defBounds _                             = []

{-
--------------------------------------------------------------------------------
coreDefs     :: [CoreBind] -> [Def]
--------------------------------------------------------------------------------
coreDefs cbs = tracepp "coreDefs" $
               L.sort [D l l' x | b <- cbs
                                , x <- bindersOf b
                                , isGoodSrcSpan (getSrcSpan x)
                                , (l, l') <- coreDef b]

coreDef :: CoreBind -> [(Int, Int)]
coreDef b
  | True  = tracepp ("coreDef: " ++ showpp (vs, vSp)) $ maybeToList vSp
  | False = tracepp ("coreDef: " ++ showpp (b, eSp, vSp)) $ meetSpans b eSp vSp
  where
    eSp   = lineSpan b $ catSpans b $ bindSpans b
    vSp   = lineSpan b $ catSpans b $ getSrcSpan <$> vs
    vs    = bindersOf b

meetSpans :: Maybe (Int, Int) -> Maybe (Int, Int) -> Maybe (Int, Int)
meetSpans Nothing       _
  = Nothing
meetSpans (Just (l,l')) Nothing
  = Just (l, l')
meetSpans (Just (l,l')) (Just (m,_))
  = Just (max l m, l')
-}
--------------------------------------------------------------------------------
-- | `meetSpans` cuts off the start-line to be no less than the line at which
--   the binder is defined. Without this, i.e. if we ONLY use the ticks and
--   spans appearing inside the definition of the binder (i.e. just `eSp`)
--   then the generated span can be WAY before the actual definition binder,
--   possibly due to GHC INLINE pragmas or dictionaries OR ...
--   for an example: see the "INCCHECK: Def" generated by
--      liquid -d benchmarks/bytestring-0.9.2.1/Data/ByteString.hs
--   where `spanEnd` is a single line function around 1092 but where
--   the generated span starts mysteriously at 222 where Data.List is imported.

meetSpans :: Maybe (Int, Int) -> Maybe (Int, Int) -> Maybe (Int, Int)
meetSpans Nothing       _
  = Nothing
meetSpans (Just (l,l')) Nothing
  = Just (l, l')
meetSpans (Just (l,l')) (Just (m, m'))
  = Just (max l m, min l' m')

-- spanLower :: Maybe (Int, Int) -> Maybe Int -> Maybe (Int, Int)
-- spanLower Nothing        _        = Nothing
-- spanLower sp             Nothing  = sp
-- spanLower (Just (l, l')) (Just m) = Just (max l m, l')

-- spanUpper :: Maybe (Int, Int) -> Maybe Int -> Maybe (Int, Int)
-- spanUpper Nothing        _        = Nothing
-- spanUpper sp             Nothing  = sp
-- spanUpper (Just (l, l')) (Just m) = Just (l, min l' m)



lineSpan :: t -> SrcSpan -> Maybe (Int, Int)
lineSpan _ (RealSrcSpan sp _) = Just (srcSpanStartLine sp, srcSpanEndLine sp)
lineSpan _ _                  = Nothing

catSpans :: Var -> [SrcSpan] -> SrcSpan
catSpans b []               = panic Nothing $ "DIFFCHECK: catSpans: no spans found for " ++ showPpr b
catSpans b xs               = foldr combineSrcSpans noSrcSpan [x | x@(RealSrcSpan z _) <- xs, varFile b == srcSpanFile z]

-- bindFile
--   :: (Outputable r, NamedThing r) =>
--      Bind r -> FastString
-- bindFile (NonRec x _) = varFile x
-- bindFile (Rec xes)    = varFile $ fst $ head xes

varFile :: (Outputable a, NamedThing a) => a -> FastString
varFile b = case getSrcSpan b of
              RealSrcSpan z _ -> srcSpanFile z
              _               -> panic Nothing $ "DIFFCHECK: getFile: no file found for: " ++ showPpr b


bindSpans :: NamedThing a => Bind a -> [SrcSpan]
bindSpans (NonRec x e)    = getSrcSpan x : exprSpans e
bindSpans (Rec    xes)    = map getSrcSpan xs ++ concatMap exprSpans es
  where
    (xs, es)              = unzip xes

exprSpans :: NamedThing a => Expr a -> [SrcSpan]
exprSpans (Tick t e)
  | isJunkSpan sp         = exprSpans e
  | otherwise             = [sp]
  where
    sp                    = tickSrcSpan t

exprSpans (Var x)         = [getSrcSpan x]
exprSpans (Lam x e)       = getSrcSpan x : exprSpans e
exprSpans (App e a)       = exprSpans e ++ exprSpans a
exprSpans (Let b e)       = bindSpans b ++ exprSpans e
exprSpans (Cast e _)      = exprSpans e
exprSpans (Case e x _ cs) = getSrcSpan x : exprSpans e ++ concatMap altSpans cs
exprSpans _               = []

altSpans :: (NamedThing b) => Alt b -> [SrcSpan]
altSpans (Alt _ xs e)     = map getSrcSpan xs ++ exprSpans e

isJunkSpan :: SrcSpan -> Bool
isJunkSpan RealSrcSpan{} = False
isJunkSpan _             = True

--------------------------------------------------------------------------------
-- | Diff Interface ------------------------------------------------------------
--------------------------------------------------------------------------------
-- | `lineDiff new old` compares the contents of `src` with `dst`
--   and returns the lines of `src` that are different.
--------------------------------------------------------------------------------
lineDiff :: FilePath -> FilePath -> IO ([Int], LMap)
--------------------------------------------------------------------------------
lineDiff new old  = lineDiff' <$> getLines new <*> getLines old
  where
    getLines      = fmap lines . readFile

lineDiff' :: [String] -> [String] -> ([Int], LMap)
lineDiff' new old = (changedLines, lm)
  where
    changedLines  = diffLines 1 diffLineCount
    lm            = foldr setShift IM.empty $ diffShifts diffLineCount
    diffLineCount = diffMap length <$> getGroupedDiff new old

diffMap :: (a -> b) -> Diff a -> Diff b
diffMap f (First x)  = First (f x)
diffMap f (Second x) = Second (f x)
diffMap f (Both x y) = Both (f x) (f y)

-- | Identifies lines that have changed
diffLines :: Int        -- ^ Starting line
          -> [Diff Int] -- ^ List of lengths of diffs
          -> [Int]      -- ^ List of changed line numbers
diffLines _ []                        = []
diffLines curr (Both lnsUnchgd _ : d) = diffLines toSkip d
   where toSkip = curr + lnsUnchgd
diffLines curr (First lnsChgd : d)    = [curr..(toTake-1)] ++ diffLines toTake d
   where toTake = curr + lnsChgd
diffLines curr (_ : d)                = diffLines curr d

diffShifts :: [Diff Int] -> [(Int, Int, Int)]
diffShifts = go 1 1
  where
    go old new (Both n _ : d) = (old, old + n - 1, new - old) : go (old + n)
                                                                   (new + n)
                                                                   d
    go old new (Second n : d) = go (old + n) new d
    go old new (First n  : d) = go old (new + n) d
    go _   _   []             = []


-- | @save@ creates an .saved version of the @target@ file, which will be
--    used to find what has changed the /next time/ @target@ is checked.
--------------------------------------------------------------------------------
saveResult :: FilePath -> Output Doc -> IO ()
--------------------------------------------------------------------------------
saveResult target res = do
  copyFile target saveF
  B.writeFile errF $ LB.toStrict $ encode res
  where
    saveF = extFileName Saved  target
    errF  = extFileName Cache  target

--------------------------------------------------------------------------------
loadResult   :: FilePath -> IO (Output Doc)
--------------------------------------------------------------------------------
loadResult f = do
  ex <- doesFileExist jsonF
  if ex
    then convert <$> B.readFile jsonF
    else return mempty
  where
    convert  = fromMaybe mempty . decode . LB.fromStrict
    jsonF    = extFileName Cache f

--------------------------------------------------------------------------------
adjustOutput :: LMap -> ChkItv -> Output Doc -> Output Doc
--------------------------------------------------------------------------------
adjustOutput lm cm o  = mempty { o_types  = adjustTypes  lm cm (o_types  o) }
                               { o_result = adjustResult lm cm (o_result o) }

adjustTypes :: LMap -> ChkItv -> AnnInfo a -> AnnInfo a
adjustTypes lm cm (AI m)          = AI $ if True then mempty else M.fromList -- FIXME PLEASE
                                    [(sp', v) | (sp, v)  <- M.toList m
                                              , Just sp' <- [adjustSrcSpan lm cm sp]]

adjustResult :: LMap -> ChkItv -> ErrorResult -> ErrorResult
adjustResult lm cm (Unsafe s es)  = errorsResult (Unsafe s)  $ mapMaybe (adjustError  lm cm) es
adjustResult lm cm (Crash es z)   = errorsResult (`Crash` z) $ (, Nothing) <$>mapMaybe (adjustError lm cm . fst) es
adjustResult _  _  r              = r

errorsResult :: ([a] -> FixResult b) -> [a] -> FixResult b
errorsResult _ []                 = Safe mempty
errorsResult f es                 = f es

adjustError :: (PPrint (TError a)) => LMap -> ChkItv -> TError a -> Maybe (TError a)
adjustError lm cm e = case adjustSrcSpan lm cm (pos e) of
  Just sp' -> Just (e {pos = sp'})
  Nothing  -> Nothing

--------------------------------------------------------------------------------
adjustSrcSpan :: LMap -> ChkItv -> SrcSpan -> Maybe SrcSpan
--------------------------------------------------------------------------------
adjustSrcSpan lm cm sp
  = do sp' <- adjustSpan lm sp
       if isCheckedSpan cm sp'
         then Nothing
         else Just sp'

isCheckedSpan :: IM.IntervalMap Int a -> SrcSpan -> Bool
isCheckedSpan cm (RealSrcSpan sp _) = isCheckedRealSpan cm sp
isCheckedSpan _  _                  = False

isCheckedRealSpan :: IM.IntervalMap Int a -> RealSrcSpan -> Bool
isCheckedRealSpan cm              = not . null . (`IM.search` cm) . srcSpanStartLine

adjustSpan :: LMap -> SrcSpan -> Maybe SrcSpan
adjustSpan lm (RealSrcSpan rsp _) = RealSrcSpan <$> adjustReal lm rsp <*> pure Nothing
adjustSpan _  sp                  = Just sp

adjustReal :: LMap -> RealSrcSpan -> Maybe RealSrcSpan
adjustReal lm rsp
  | Just δ <- sh                  = Just $ packRealSrcSpan f (l1 + δ) c1 (l2 + δ) c2
  | otherwise                     = Nothing
  where
    (f, l1, c1, l2, c2)           = unpackRealSrcSpan rsp
    sh                            = getShift l1 lm


-- | @getShift lm old@ returns @Just δ@ if the line number @old@ shifts by @δ@
-- in the diff and returns @Nothing@ otherwise.
getShift     :: Int -> LMap -> Maybe Int
getShift old = fmap snd . listToMaybe . IM.search old

-- | @setShift (lo, hi, δ) lm@ updates the interval map @lm@ appropriately
setShift             :: (Int, Int, Int) -> LMap -> LMap
setShift (l1, l2, δ) = IM.insert (IM.Interval l1 l2) δ


checkedItv :: [Def] -> ChkItv
checkedItv chDefs = foldr (`IM.insert` ()) IM.empty is
  where
    is            = [IM.Interval l1 l2 | D l1 l2 _ <- chDefs]


--------------------------------------------------------------------------------
-- | Aeson instances -----------------------------------------------------------
--------------------------------------------------------------------------------

instance ToJSON SourcePos where
  toJSON p = object [   "sourceName"   .= f
                      , "sourceLine"   .= unPos l
                      , "sourceColumn" .= unPos c
                      ]
             where
               f    = sourceName   p
               l    = sourceLine   p
               c    = sourceColumn p

instance FromJSON SourcePos where
  parseJSON (Object v) = safeSourcePos <$> v .: "sourceName"
                                <*> v .: "sourceLine"
                                <*> v .: "sourceColumn"
  parseJSON _          = mempty

instance FromJSON ErrorResult

instance ToJSON Doc where
  toJSON = String . T.pack . render

instance FromJSON Doc where
  parseJSON (String s) = return $ text $ T.unpack s
  parseJSON _          = mempty

instance ToJSON a => ToJSON (AnnInfo a) where
  toJSON = genericToJSON defaultOptions
  toEncoding = genericToEncoding defaultOptions
instance FromJSON a => FromJSON (AnnInfo a)

instance ToJSON (Output Doc) where
  toJSON = genericToJSON defaultOptions
  toEncoding = genericToEncoding defaultOptions
instance FromJSON (Output Doc) where
  parseJSON = genericParseJSON defaultOptions

file :: Located a -> FilePath
file = sourceName . loc

line :: Located a -> Int
line  = unPos . sourceLine . loc

lineE :: Located a -> Int
lineE = unPos . sourceLine . locE
