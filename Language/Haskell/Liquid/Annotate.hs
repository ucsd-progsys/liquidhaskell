{-# LANGUAGE DeriveDataTypeable #-}
-- MultiParamTypeClasses, NoMonomorphismRestriction, TypeSynonymInstances, FlexibleInstances, TupleSections, , ScopedTypeVariables 


-- | This module contains the code that uses the inferred types to generate
-- htmlized source with mouseover annotations.

module Language.Haskell.Liquid.Annotate (
  -- * Types representing annotations
    AnnInfo (..)
  , Annot

  -- * Top-level annotation renderer function
  ,  annotate
  ) where

import GHC                      ( SrcSpan (..)
                                , srcSpanStartCol
                                , srcSpanEndCol
                                , srcSpanStartLine
                                , srcSpanEndLine) 

import Var                      (Var (..))                                
import Outputable
import GHC.Exts                 (groupWith, sortWith)

import Data.Char                (isSpace)

import Control.Arrow            hiding ((<+>))
import Control.Applicative      ((<$>))
-- import Data.Data                hiding (TyCon, tyConName)

import System.FilePath          (takeFileName, dropFileName, (</>)) 
import System.Directory         (findExecutable)
import System.Directory         (copyFile) 

import Text.Printf              (printf)
import qualified Data.Text  as T
import qualified Data.HashMap.Strict   as M

import qualified Language.Haskell.Liquid.ACSS as ACSS
import Language.Haskell.HsColour.Classify
import Language.Haskell.Liquid.FileNames
import Language.Haskell.Liquid.Fixpoint
import Language.Haskell.Liquid.RefType
import Language.Haskell.Liquid.Tidy
import Language.Haskell.Liquid.Misc

-------------------------------------------------------------------
------ Rendering HTMLized source with Inferred Types --------------
-------------------------------------------------------------------

annotate :: FilePath -> FixSolution -> AnnInfo Annot -> IO ()
annotate fname sol anna 
  = do annotDump fname (extFileName Html $ extFileName Cst fname) annm
       annotDump fname (extFileName Html fname) annm'
    where annm  = closeAnnots anna
          annm' = tidyRefType <$> applySolution sol annm

annotDump :: FilePath -> FilePath -> AnnInfo RefType -> IO ()
annotDump srcFile htmlFile ann 
  = do let annm    = mkAnnMap ann
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
  = do _  <- writeFile mdFile $ pandocPreProc css body
       ec <- executeShellCommand "pandoc" cmd 
       checkExitCode cmd ec
    where mdFile = extFileName Mkdn srcFile 
          cmd    = pandocCmd pandocPath mdFile htmlFile

pandocCmd pandocPath mdFile htmlFile
  = printf "%s -f markdown -t html %s > %s" pandocPath mdFile htmlFile  

pandocPreProc css
  = T.unpack 
  . T.append (T.pack $ cssHTML css) 
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
  = writeFile htmlFile $ (top'n'tail srcFile css $! body)

top'n'tail title css = (htmlHeader title css ++) . (++ htmlClose)

htmlHeader title css = unlines
  [ "<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 3.2 Final//EN\">"
  , "<html>"
  , "<head>"
  , "<title>" ++ title ++ "</title>"
  , "</head>"
  , cssHTML css
  , "<body>"
  -- , "<h1>Liquid Types: " ++ title ++ "</h1>"
  , "<hr>"
  , "Put mouse over identifiers to see inferred types"
  ]

htmlClose  = "\n</body>\n</html>"

cssHTML css = unlines
  [ "<head>"
  -- , "<style media=\"screen\" type=\"text/css\">"
  -- , css
  -- , "</style>"
  , "<link type='text/css' rel='stylesheet' href='"++ css ++ "' />"
  , "</head>"
  ]
  


------------------------------------------------------------------------------
-- | Building Annotation Maps ------------------------------------------------
------------------------------------------------------------------------------

-- | This function converts our annotation information into that which is
-- required by `Language.Haskell.HsColour.ACSS` to generate mouseover
-- annotations.

mkAnnMap :: AnnInfo RefType -> ACSS.AnnMap
mkAnnMap (AI m) 
  = ACSS.Ann 
  $ M.fromList
  $ map (srcSpanLoc *** bindString)
  $ map (head . sortWith (srcSpanEndCol . fst)) 
  $ groupWith (lineCol . fst) 
  $ [ (l, m) | (RealSrcSpan l, m) <- M.toList m, oneLine l]  
  where bindString = mapPair (showSDocForUser neverQualify) . pprXOT 

srcSpanLoc l 
  = ACSS.L (srcSpanStartLine l, srcSpanStartCol l)
oneLine l  
  = srcSpanStartLine l == srcSpanEndLine l
lineCol l  
  = (srcSpanStartLine l, srcSpanStartCol l)

closeAnnots :: AnnInfo Annot -> AnnInfo RefType 
closeAnnots = fmap uRType' . closeA . filterA
  
closeA a@(AI m)  = cf <$> a 
  where cf (Right loc) = case m `mlookup` loc of
                           (_, Left t) -> t
                           _           -> errorstar $ "malformed AnnInfo: " ++ showPpr loc
        cf (Left t)    = t

filterA (AI m) = AI (M.filter ff m)
  where ff (_, Right loc) = loc `M.member` m
        ff _              = True

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

newtype AnnInfo a = AI (M.HashMap SrcSpan (Maybe Var, a))
    -- deriving (Data, Typeable)

type Annot 
  = Either SpecType SrcSpan
    -- deriving (Data, Typeable)

instance Functor AnnInfo where
  fmap f (AI m) = AI (fmap (\(x, y) -> (x, f y)) m)

instance Outputable a => Outputable (AnnInfo a) where
  ppr (AI m) = vcat $ map pprAnnInfoBind $ M.toList m 
 

pprAnnInfoBind (RealSrcSpan k, xv) 
  = xd $$ ppr l $$ ppr c $$ ppr n $$ vd $$ text "\n\n\n"
    where l        = srcSpanStartLine k
          c        = srcSpanStartCol k
          (xd, vd) = pprXOT xv 
          n        = length $ lines $ showSDoc vd

pprAnnInfoBind (_, _) 
  = empty

pprXOT (x, v) = (xd, ppr v)
  where xd = maybe (text "unknown") ppr x

applySolution :: FixSolution -> AnnInfo RefType -> AnnInfo RefType 
applySolution = fmap . fmap . mapReft . map . appSolRefa 
  where appSolRefa _ ra@(RConc _) = ra 
        -- appSolRefa _ p@(RPvar _)  = p  
        appSolRefa s (RKvar k su) = RConc $ subst su $ M.lookupDefault PTop k s  
        mapReft f (Reft (x, zs))  = Reft (x, squishRas $ f zs)

squishRas ras  = (squish [p | RConc p <- ras]) : []
  where squish = RConc . pAnd . sortNub . filter (not . isTautoPred) . concatMap conjuncts   

conjuncts (PAnd ps)          = concatMap conjuncts ps
conjuncts p | isTautoPred p  = []
            | otherwise      = [p]


