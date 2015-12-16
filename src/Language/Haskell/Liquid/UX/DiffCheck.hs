-- | This module contains the code for Incremental checking, which finds the
--   part of a target file (the subset of the @[CoreBind]@ that have been
--   modified since it was last checked, as determined by a diff against
--   a saved version of the file.

{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}

module Language.Haskell.Liquid.UX.DiffCheck (

   -- * Changed binders + Unchanged Errors
     DiffCheck (..)

   -- * Use previously saved info to generate DiffCheck target
   , slice

   -- * Use target binders to generate DiffCheck target
   , thin

   -- * Save current information for next time
   , saveResult

   )
   where

--import            Debug.Trace (trace)
import            Control.Applicative          ((<$>), (<*>))
import            Data.Aeson
import qualified  Data.Text as T
import            Data.Algorithm.Diff
import            Data.Monoid                   (mempty)
import            Data.Maybe                    (listToMaybe, mapMaybe, fromMaybe)
import            Data.Hashable
import qualified  Data.IntervalMap.FingerTree as IM
import            CoreSyn                       hiding (sourceName)
import            Name
import            SrcLoc hiding (Located)
import            Var
import qualified  Data.HashSet                  as S
import qualified  Data.HashMap.Strict           as M
import qualified  Data.List                     as L
import            System.Directory                (copyFile, doesFileExist)
import            Language.Fixpoint.Types         (FixResult (..), Located (..))
import            Language.Fixpoint.Utils.Files
import            Language.Haskell.Liquid.Types   (SpecType, GhcSpec (..), AnnInfo (..), DataConP (..), Error, TError (..), Output (..))
import            Language.Haskell.Liquid.Misc    (mkGraph)
import            Language.Haskell.Liquid.GHC.Misc
import            Language.Haskell.Liquid.Types.Visitors
import            Language.Haskell.Liquid.UX.Errors   ()
import            Text.Parsec.Pos                  (sourceName, sourceLine, sourceColumn, SourcePos, newPos)
import            Text.PrettyPrint.HughesPJ        (text, render, Doc)

import qualified  Data.ByteString               as B
import qualified  Data.ByteString.Lazy          as LB


-------------------------------------------------------------------------
-- Data Types -----------------------------------------------------------
-------------------------------------------------------------------------

-- | Main type of value returned for diff-check.
data DiffCheck = DC { newBinds  :: [CoreBind]
                    , oldOutput :: !(Output Doc)
                    , newSpec   :: !GhcSpec
                    }

-- | Variable definitions
data Def  = D { start  :: Int -- ^ line at which binder definition starts
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



-------------------------------------------------------------------------
-- | `slice` returns a subset of the @[CoreBind]@ of the input `target`
--    file which correspond to top-level binders whose code has changed
--    and their transitive dependencies.
-------------------------------------------------------------------------
slice :: FilePath -> [CoreBind] -> GhcSpec -> IO (Maybe DiffCheck)
-------------------------------------------------------------------------
slice target cbs sp = ifM (doesFileExist savedFile)
                          doDiffCheck
                          (return Nothing)
  where
    savedFile       = extFileName Saved target
    doDiffCheck     = sliceSaved target savedFile cbs sp

sliceSaved :: FilePath -> FilePath -> [CoreBind] -> GhcSpec -> IO (Maybe DiffCheck)
sliceSaved target savedFile coreBinds spec
  = do (is, lm) <- lineDiff target savedFile
       result   <- loadResult target
       return    $ sliceSaved' is lm (DC coreBinds result spec)

sliceSaved' :: [Int] -> LMap -> DiffCheck -> Maybe DiffCheck
sliceSaved' is lm (DC coreBinds result spec)
  | globalDiff is spec = Nothing
  | otherwise          = Just $ DC cbs' res' sp'
  where
    cbs'             = thinWith sigs coreBinds $ diffVars is dfs
    sigs             = S.fromList $ M.keys sigm
    sigm             = sigVars is spec
    res'             = adjustOutput lm cm result
    cm               = checkedItv chDfs
    dfs              = coreDefs coreBinds ++ specDefs spec
    chDfs            = coreDefs cbs'
    sp'              = assumeSpec sigm spec

-- Add the specified signatures for vars-with-preserved-sigs,
-- whose bodies have been pruned from [CoreBind] into the "assumes"
assumeSpec :: M.HashMap Var (Located SpecType) -> GhcSpec -> GhcSpec
assumeSpec sigm sp = sp { asmSigs = M.toList $ M.union sigm assm }
  where
    assm           = M.fromList $ asmSigs sp
    -- sigm'       = trace ("INCCHECK: sigm = " ++ show zs) sigm
    -- zs          = M.keys sigm

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

sigVars :: [Int] -> GhcSpec -> M.HashMap Var (Located SpecType)
sigVars ls sp = M.fromList $ filter (ok . snd) $ specSigs sp
  where
    ok        = not . isDiff ls

globalDiff :: [Int] -> GhcSpec -> Bool
globalDiff lines spec = measDiff || invsDiff || dconsDiff
  where
    measDiff  = any (isDiff lines) (snd <$> meas spec)
    invsDiff  = any (isDiff lines) (invariants spec)
    dconsDiff = any (isDiff lines) (dloc . snd <$> dconsP spec)
    dloc dc   = Loc (dc_loc dc) (dc_locE dc) ()

isDiff :: [Int] -> Located a -> Bool
isDiff lines x = any hits lines
  where
    hits i = line x <= i && i <= lineE x

-------------------------------------------------------------------------
-- | @thin@ returns a subset of the @[CoreBind]@ given which correspond
--   to those binders that depend on any of the @Var@s provided.
-------------------------------------------------------------------------
thin :: [CoreBind] -> [Var] -> [CoreBind]
-------------------------------------------------------------------------
thin = thinWith S.empty

thinWith :: S.HashSet Var -> [CoreBind] -> [Var] -> [CoreBind]
thinWith sigs cbs xs = filterBinds cbs ys
  where
     ys       = calls `S.union` calledBy
     calls    = txClosure (coreDeps cbs) sigs (S.fromList xs)
     calledBy = dependsOn (coreDeps cbs) xs

coreDeps    :: [CoreBind] -> Deps
coreDeps bs = mkGraph $ calls ++ calls'
  where
    calls   = concatMap deps bs
    calls'  = [(y, x) | (x, y) <- calls]
    deps b  = [(x, y) | x <- bindersOf b
                      , y <- freeVars S.empty b]
-- Given a call graph, and a list of vars, this function checks all functions
-- to see if they call any of the functions in the vars list. If any do, then
-- they must also be rechecked.
dependsOn :: Deps -> [Var] -> S.HashSet Var
dependsOn cg vars = S.fromList results
   where
      preds = map S.member vars
      filteredMaps = M.filter <$> preds <*> pure cg
      results = map fst $ M.toList $ M.unions filteredMaps

txClosure :: Deps -> S.HashSet Var -> S.HashSet Var -> S.HashSet Var
txClosure d sigs xs = go S.empty xs
  where
    next           = S.unions . fmap deps . S.toList
    deps x         = M.lookupDefault S.empty x d
    go seen new
      | S.null new = seen
      | otherwise  = let seen' = S.union seen new
                         new'  = next new `S.difference` seen'
                         new'' = new'  `S.difference` sigs
                     in go seen' new''



-------------------------------------------------------------------------
filterBinds        :: [CoreBind] -> S.HashSet Var -> [CoreBind]
-------------------------------------------------------------------------
filterBinds cbs ys = filter f cbs
  where
    f (NonRec x _) = x `S.member` ys
    f (Rec xes)    = any (`S.member` ys) $ fst <$> xes


-------------------------------------------------------------------------
specDefs :: GhcSpec -> [Def]
-------------------------------------------------------------------------
specDefs       = map def . specSigs
  where
    def (x, t) = D (line t) (lineE t) x

specSigs :: GhcSpec -> [(Var, Located SpecType)]
specSigs sp = tySigs sp ++ asmSigs sp ++ ctors sp

-------------------------------------------------------------------------
coreDefs     :: [CoreBind] -> [Def]
-------------------------------------------------------------------------
coreDefs cbs = L.sort [D l l' x | b <- cbs
                                , x <- bindersOf b
                                , isGoodSrcSpan (getSrcSpan x)
                                , (l, l') <- coreDef b]
coreDef b    = meetSpans b eSp vSp
  where
    eSp      = lineSpan b $ catSpans b $ bindSpans b
    vSp      = lineSpan b $ catSpans b $ getSrcSpan <$> bindersOf b


-------------------------------------------------------------------------
-- | `meetSpans` cuts off the start-line to be no less than the line at which
--   the binder is defined. Without this, i.e. if we ONLY use the ticks and
--   spans appearing inside the definition of the binder (i.e. just `eSp`)
--   then the generated span can be WAY before the actual definition binder,
--   possibly due to GHC INLINE pragmas or dictionaries OR ...
--   for an example: see the "INCCHECK: Def" generated by
--      liquid -d benchmarks/bytestring-0.9.2.1/Data/ByteString.hs
--   where `spanEnd` is a single line function around 1092 but where
--   the generated span starts mysteriously at 222 where Data.List is imported.

meetSpans _ Nothing       _
  = []
meetSpans _ (Just (l,l')) Nothing
  = [(l, l')]
meetSpans _ (Just (l,l')) (Just (m,_))
  = [(max l m, l')]

lineSpan _ (RealSrcSpan sp) = Just (srcSpanStartLine sp, srcSpanEndLine sp)
lineSpan _ _                = Nothing

catSpans b []               = error $ "DIFFCHECK: catSpans: no spans found for " ++ showPpr b
catSpans b xs               = foldr combineSrcSpans noSrcSpan [x | x@(RealSrcSpan z) <- xs, bindFile b == srcSpanFile z]

bindFile (NonRec x _) = varFile x
bindFile (Rec xes)    = varFile $ fst $ head xes

varFile b = case getSrcSpan b of
              RealSrcSpan z -> srcSpanFile z
              _             -> error $ "DIFFCHECK: getFile: no file found for: " ++ showPpr b


bindSpans (NonRec x e)    = getSrcSpan x : exprSpans e
bindSpans (Rec    xes)    = map getSrcSpan xs ++ concatMap exprSpans es
  where
    (xs, es)              = unzip xes

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

altSpans (_, xs, e)       = map getSrcSpan xs ++ exprSpans e

isJunkSpan (RealSrcSpan _) = False
isJunkSpan _               = True

-------------------------------------------------------------------------
-- | Diff Interface -----------------------------------------------------
-------------------------------------------------------------------------


-- | `lineDiff new old` compares the contents of `src` with `dst`
--   and returns the lines of `src` that are different.
-------------------------------------------------------------------------
lineDiff :: FilePath -> FilePath -> IO ([Int], LMap)
-------------------------------------------------------------------------
lineDiff new old  = lineDiff' <$> getLines new <*> getLines old
  where
    getLines      = fmap lines . readFile

lineDiff' :: [String] -> [String] -> ([Int], LMap)
lineDiff' new old = (changedLines, lm)
  where
    changedLines  = diffLines 1 diffLineCount
    lm            = foldr setShift IM.empty $ diffShifts diffLineCount
    diffLineCount = fmap length <$> getGroupedDiff new old

-- | Identifies lines that have changed
diffLines :: Int -- ^ Starting line
             -> [Diff Int] -- ^ List of lengths of diffs
             -> [Int] -- ^ List of changed line numbers
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

instance Functor Diff where
  fmap f (First x)  = First (f x)
  fmap f (Second x) = Second (f x)
  fmap f (Both x y) = Both (f x) (f y)

-- | @save@ creates an .saved version of the @target@ file, which will be
--    used to find what has changed the /next time/ @target@ is checked.
-------------------------------------------------------------------------
saveResult :: FilePath -> Output Doc -> IO ()
-------------------------------------------------------------------------
saveResult target res
  = do copyFile target saveF
       B.writeFile errF $ LB.toStrict $ encode res
    where
       saveF = extFileName Saved  target
       errF  = extFileName Cache  target

-------------------------------------------------------------------------
loadResult   :: FilePath -> IO (Output Doc)
-------------------------------------------------------------------------
loadResult f = ifM (doesFileExist jsonF) out (return mempty)
  where
    jsonF    = extFileName Cache f
    out      = (fromMaybe mempty . decode . LB.fromStrict) <$> B.readFile jsonF

-------------------------------------------------------------------------
adjustOutput :: LMap -> ChkItv -> Output Doc -> Output Doc
-------------------------------------------------------------------------
adjustOutput lm cm o  = mempty { o_types  = adjustTypes  lm cm (o_types  o) }
                               { o_result = adjustResult lm cm (o_result o) }

adjustTypes :: LMap -> ChkItv -> AnnInfo a -> AnnInfo a
adjustTypes lm cm (AI m)          = AI $ M.fromList
                                    [(sp', v) | (sp, v)  <- M.toList m
                                              , Just sp' <- [adjustSrcSpan lm cm sp]]

adjustResult :: LMap -> ChkItv -> FixResult Error -> FixResult Error
adjustResult lm cm (Unsafe es)    = errorsResult Unsafe      $ adjustErrors lm cm es
adjustResult lm cm (Crash es z)   = errorsResult (`Crash` z) $ adjustErrors lm cm es
adjustResult _  _  r              = r

errorsResult :: ([a] -> FixResult b) -> [a] -> FixResult b
errorsResult _ []                 = Safe
errorsResult f es                 = f es

adjustErrors :: LMap -> ChkItv -> [TError a] -> [TError a]
adjustErrors lm cm                = mapMaybe adjustError
  where
    adjustError (ErrSaved sp m)   =  (`ErrSaved` m) <$> adjustSrcSpan lm cm sp
    adjustError e                 = Just e

-------------------------------------------------------------------------
adjustSrcSpan :: LMap -> ChkItv -> SrcSpan -> Maybe SrcSpan
-------------------------------------------------------------------------
adjustSrcSpan lm cm sp
  = do sp' <- adjustSpan lm sp
       if isCheckedSpan cm sp'
         then Nothing
         else Just sp'

isCheckedSpan cm (RealSrcSpan sp) = isCheckedRealSpan cm sp
isCheckedSpan _  _                = False
isCheckedRealSpan cm              = not . null . (`IM.search` cm) . srcSpanStartLine

adjustSpan lm (RealSrcSpan rsp)   = RealSrcSpan <$> adjustReal lm rsp
adjustSpan _  sp                  = Just sp
adjustReal lm rsp
  | Just δ <- getShift l1 lm      = Just $ realSrcSpan f (l1 + δ) c1 (l2 + δ) c2
  | otherwise                     = Nothing
  where
    (f, l1, c1, l2, c2)           = unpackRealSrcSpan rsp


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


-------------------------------------------------------------------------
-- | Aeson instances ----------------------------------------------------
-------------------------------------------------------------------------

instance ToJSON SourcePos where
  toJSON p = object [   "sourceName"   .= f
                      , "sourceLine"   .= l
                      , "sourceColumn" .= c
                      ]
             where
               f    = sourceName   p
               l    = sourceLine   p
               c    = sourceColumn p

instance FromJSON SourcePos where
  parseJSON (Object v) = newPos <$> v .: "sourceName"
                                <*> v .: "sourceLine"
                                <*> v .: "sourceColumn"
  parseJSON _          = mempty


instance ToJSON (FixResult Error)
instance FromJSON (FixResult Error)

instance ToJSON Doc where
  toJSON = String . T.pack . render

instance FromJSON Doc where
  parseJSON (String s) = return $ text $ T.unpack s
  parseJSON _          = mempty

instance (ToJSON k, ToJSON v) => ToJSON (M.HashMap k v) where
  toJSON = toJSON . M.toList

instance (Eq k, Hashable k, FromJSON k, FromJSON v) => FromJSON (M.HashMap k v) where
  parseJSON = fmap M.fromList . parseJSON

instance ToJSON a => ToJSON (AnnInfo a)
instance FromJSON a => FromJSON (AnnInfo a)

instance ToJSON (Output Doc)
instance FromJSON (Output Doc)


line :: Located a -> Int
line  = sourceLine . loc

lineE :: Located a -> Int
lineE = sourceLine . locE

-------------------------------------------------------------------------
---- Helper functions ---------------------------------------------------
-------------------------------------------------------------------------

ifM :: (Monad m) => m Bool -> m b -> m b -> m b
ifM b x y = b >>= \z -> if z then x else y
