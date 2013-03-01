{-# LANGUAGE DeriveDataTypeable, TupleSections #-}
-- MultiParamTypeClasses, NoMonomorphismRestriction, TypeSynonymInstances, FlexibleInstances, TupleSections, , ScopedTypeVariables 


-- | This module contains the code that uses the inferred types to generate
-- htmlized source with mouseover annotations.

module Language.Haskell.Liquid.Annotate (
  -- * Types representing annotations
    AnnInfo (..)
  , Annot (..)

  -- * Top-level annotation renderer function
  ,  annotate
  ) where

import GHC                      ( SrcSpan (..)
                                , srcSpanStartCol
                                , srcSpanEndCol
                                , srcSpanStartLine
                                , srcSpanEndLine) 

import Var                      (Var (..))                                
import Outputable               (showPpr)
import Text.PrettyPrint.HughesPJ
import GHC.Exts                 (groupWith, sortWith)

import Data.Char                (isSpace)

import Control.Arrow            hiding ((<+>))
import Control.Applicative      ((<$>))
import Control.DeepSeq
-- import Data.Data                hiding (TyCon, tyConName)

import System.FilePath          (takeFileName, dropFileName, (</>)) 
import System.Directory         (findExecutable)
import System.Directory         (copyFile) 

import Text.Printf              (printf)
import qualified Data.Text  as T
import qualified Data.HashMap.Strict   as M

import qualified Language.Haskell.Liquid.ACSS as ACSS
import Language.Haskell.HsColour.Classify

import Language.Fixpoint.Files
import Language.Fixpoint.Names
import Language.Fixpoint.Misc

import Language.Haskell.Liquid.GhcMisc (pprDoc)
import Language.Fixpoint.Types
import Language.Haskell.Liquid.RefType
import Language.Haskell.Liquid.Tidy

-------------------------------------------------------------------
------ Rendering HTMLized source with Inferred Types --------------
-------------------------------------------------------------------

annotate :: FilePath -> FixResult SrcSpan -> FixSolution -> AnnInfo Annot -> IO ()
annotate fname result sol anna 
  = do annotDump fname (extFileName Html $ extFileName Cst fname) result annm
       annotDump fname (extFileName Html fname) result annm'
    where annm = closeAnnots anna
          annm' = tidySpecType <$> applySolution sol annm

annotDump :: FilePath -> FilePath -> FixResult SrcSpan -> AnnInfo SpecType -> IO ()
annotDump srcFile htmlFile result ann
  = do let annm    = mkAnnMap result ann
       let annFile = extFileName Annot srcFile
       writeFilesOrStrings   annFile [Left srcFile, Right (show annm)]
       annotHtmlDump         htmlFile srcFile annm 
       return ()

writeFilesOrStrings :: FilePath -> [Either FilePath String] -> IO ()
writeFilesOrStrings tgtFile = mapM_ $ either (`copyFile` tgtFile) (tgtFile `appendFile`) 

annotHtmlDump htmlFile srcFile annm
  = do src     <- readFile srcFile
       let lhs  = isExtFile LHs srcFile
       let body = {-# SCC "hsannot" #-} ACSS.hsannot False (Just tokAnnot) lhs (src, annm)
       cssFile <- getCSSPath
       copyFile cssFile (dropFileName htmlFile </> takeFileName cssFile) 
       renderHtml lhs htmlFile srcFile (takeFileName cssFile) body

renderHtml True  = renderPandoc 
renderHtml False = renderDirect

-------------------------------------------------------------------------
-- | Pandoc HTML Rendering (for lhs + markdown source) ------------------ 
-------------------------------------------------------------------------
     
renderPandoc htmlFile srcFile css body
  = do renderFn <- maybe renderDirect renderPandoc' <$> findExecutable "pandoc"  
       renderFn htmlFile srcFile css body

renderPandoc' pandocPath htmlFile srcFile css body
  = do _  <- writeFile mdFile $ pandocPreProc body
       ec <- executeShellCommand "pandoc" cmd 
       writeFilesOrStrings htmlFile [Right (cssHTML css)]
       checkExitCode cmd ec
    where mdFile = extFileName Mkdn srcFile 
          cmd    = pandocCmd pandocPath mdFile htmlFile

pandocCmd pandocPath mdFile htmlFile
  = printf "%s -f markdown -t html %s > %s" pandocPath mdFile htmlFile  

pandocPreProc
  = T.unpack 
  -- . T.append (T.pack $ cssHTML css) 
  . stripBegin 
  . stripEnd 
  . T.pack
  where stripBegin = T.replace (T.pack "\\begin{code}") T.empty 
        stripEnd   = T.replace (T.pack "\\end{code}")   T.empty 

-------------------------------------------------------------------------
-- | Direct HTML Rendering (for non-lhs/markdown source) ---------------- 
-------------------------------------------------------------------------

-- More or less taken from hscolour

renderDirect htmlFile srcFile css body 
  = writeFile htmlFile $! (top'n'tail full srcFile css $! body)
    where full = True -- False  -- TODO: command-line-option 

-- | @top'n'tail True@ is used for standalone HTML, 
--   @top'n'tail False@ for embedded HTML

top'n'tail True  title css = (htmlHeader title css ++) . (++ htmlClose)
top'n'tail False _    _    = id

-- Use this for standalone HTML

htmlHeader title css = unlines
  [ "<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 3.2 Final//EN\">"
  , "<html>"
  , "<head>"
  , "<title>" ++ title ++ "</title>"
  , "</head>"
  , cssHTML css
  , "<body>"
  , "<hr>"
  , "Put mouse over identifiers to see inferred types"
  ]

htmlClose  = "\n</body>\n</html>"

cssHTML css = unlines
  [ "<head>"
  , "<link type='text/css' rel='stylesheet' href='"++ css ++ "' />"
  , "</head>"
  ]

------------------------------------------------------------------------------
-- | Building Annotation Maps ------------------------------------------------
------------------------------------------------------------------------------

-- | This function converts our annotation information into that which is
-- required by `Language.Haskell.Liquid.ACSS` to generate mouseover
-- annotations.

mkAnnMap ::  FixResult SrcSpan -> AnnInfo SpecType -> ACSS.AnnMap
mkAnnMap res ann = ACSS.Ann (mkAnnMapTyp ann) (mkAnnMapErr res)
    
mkAnnMapErr (Unsafe ls) = [ (srcSpanStartLoc  l, srcSpanEndLoc l) | RealSrcSpan l <- ls] 
mkAnnMapErr _           = []

mkAnnMapTyp (AI m) 
  = M.fromList
  $ map (srcSpanStartLoc *** bindString)
  $ map (head . sortWith (srcSpanEndCol . fst)) 
  $ groupWith (lineCol . fst) 
  $ [ (l, x) | (RealSrcSpan l, (x:_)) <- M.toList m, oneLine l]  
  where bindString = mapPair {- (showSDocForUser neverQualify) -} render . pprXOT 

srcSpanStartLoc l 
  = ACSS.L (srcSpanStartLine l, srcSpanStartCol l)
srcSpanEndLoc l 
  = ACSS.L (srcSpanEndLine l, srcSpanEndCol l)
oneLine l  
  = srcSpanStartLine l == srcSpanEndLine l
lineCol l  
  = (srcSpanStartLine l, srcSpanStartCol l)

closeAnnots :: AnnInfo Annot -> AnnInfo SpecType 
closeAnnots = closeA . filterA . collapseA

closeA a@(AI m)  = cf <$> a 
  where cf (Loc loc) = case m `mlookup` loc of
                           [(_, Use t)] -> t
                           [(_, Def t)] -> t
                           [(_, RDf t)] -> t
                           _            -> errorstar $ "malformed AnnInfo: " ++ showPpr loc
        cf (Use t)   = t
        cf (Def t)   = t
        cf (RDf t)   = t

filterA (AI m) = AI (M.filter ff m)
  where ff [(_, Loc loc)] = loc `M.member` m
        ff _              = True

collapseA (AI m) = AI (fmap pickOneA m)

pickOneA xas = case (rs, ds, ls, us) of
                 ((x:_), _, _, _) -> [x]
                 (_, (x:_), _, _) -> [x]
                 (_, _, (x:_), _) -> [x]
                 (_, _, _, (x:_)) -> [x]
  where 
    rs = [x | x@(_, RDf _) <- xas]
    ds = [x | x@(_, Def _) <- xas]
    ls = [x | x@(_, Loc _) <- xas]
    us = [x | x@(_, Use _) <- xas]

------------------------------------------------------------------------------
-- | Tokenizing Refinement Type Annotations in @-blocks ----------------------
------------------------------------------------------------------------------

-- | The token used for refinement symbols inside the highlighted types in @-blocks.
refToken = Keyword

-- | The top-level function for tokenizing @-block annotations. Used to
-- tokenize comments by ACSS.
tokAnnot s 
  = case trimLiquidAnnot s of 
      Just (l, body, r) -> [(refToken, l)] ++ tokBody body ++ [(refToken, r)]
      Nothing           -> [(Comment, s)]

trimLiquidAnnot ('{':'-':'@':ss) 
  | drop (length ss - 3) ss == "@-}"
  = Just ("{-@", take (length ss - 3) ss, "@-}") 
trimLiquidAnnot _  
  = Nothing

tokBody s 
  | isData s  = tokenise s
  | isType s  = tokenise s
  | isIncl s  = tokenise s
  | otherwise = tokeniseSpec s 

isData = spacePrefix "data"
isType = spacePrefix "type"
isIncl = spacePrefix "include"

spacePrefix str s@(c:cs)
  | isSpace c   = spacePrefix str cs
  | otherwise   = (take (length str) s) == str
spacePrefix _ _ = False 


tokeniseSpec = tokAlt . chopAlt [('{', ':'), ('|', '}')] 
  where tokAlt (s:ss)  = tokenise s ++ tokAlt' ss
        tokAlt _       = []
        tokAlt' (s:ss) = (refToken, s) : tokAlt ss
        tokAlt' _      = []

---------------------------------------------------------------
---------------- Annotations and Solutions --------------------
---------------------------------------------------------------

newtype AnnInfo a = AI (M.HashMap SrcSpan [(Maybe Var, a)])

data Annot        = Use SpecType 
                  | Def SpecType 
                  | RDf SpecType
                  | Loc SrcSpan

instance Functor AnnInfo where
  fmap f (AI m) = AI (fmap (fmap (\(x, y) -> (x, f y))) m)

instance Fixpoint a => Fixpoint (AnnInfo a) where
  toFix (AI m) = vcat $ map pprAnnInfoBinds $ M.toList m 

instance NFData a => NFData (AnnInfo a) where
  rnf (AI x) = () -- rnf x

instance NFData Annot where
  rnf (Def x) = () -- rnf x
  rnf (RDf x) = () -- rnf x
  rnf (Use x) = () -- rnf x
  rnf (Loc x) = () -- rnf x

instance Fixpoint Annot where
  toFix (Use t) = text "Use" <+> toFix t
  toFix (Def t) = text "Def" <+> toFix t
  toFix (RDf t) = text "RDf" <+> toFix t
  toFix (Loc l) = text "Loc" <+> pprDoc l

pprAnnInfoBinds (l, xvs) 
  = vcat $ map (pprAnnInfoBind . (l,)) xvs

pprAnnInfoBind (RealSrcSpan k, xv) 
  = xd $$ pprDoc l $$ pprDoc c $$ toFix n $$ vd $$ text "\n\n\n"
    where l        = srcSpanStartLine k
          c        = srcSpanStartCol k
          (xd, vd) = pprXOT xv 
          n        = length $ lines $ render vd

pprAnnInfoBind (_, _) 
  = empty

pprXOT (x, v) = (xd, toFix v)
  where xd = maybe (text "unknown") toFix x

applySolution :: FixSolution -> AnnInfo SpecType -> AnnInfo SpecType 
applySolution = fmap . fmap . mapReft . map . appSolRefa 
  where appSolRefa _ ra@(RConc _) = ra 
        -- appSolRefa _ p@(RPvar _)  = p  
        appSolRefa s (RKvar k su) = RConc $ subst su $ M.lookupDefault PTop k s  
        mapReft f (U (Reft (x, zs)) p) = U (Reft (x, squishRas $ f zs)) p

squishRas ras  = (squish [p | RConc p <- ras]) : []
  where squish = RConc . pAnd . sortNub . filter (not . isTautoPred) . concatMap conjuncts   

conjuncts (PAnd ps)          = concatMap conjuncts ps
conjuncts p | isTautoPred p  = []
            | otherwise      = [p]


