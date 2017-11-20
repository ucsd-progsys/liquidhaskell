module Gradual.GUI.Annotate (renderHtml) where 

import Language.Haskell.Liquid.GHC.Misc   (Loc(..))
import Language.Fixpoint.Misc (thd3)
import Language.Fixpoint.Types.Spans hiding (Loc)

-- import GHC                     ( SrcSpan (..)
--                                           , srcSpanStartCol, srcSpanEndCol, srcSpanStartLine, srcSpanEndLine)
import qualified Language.Haskell.HsColour.CSS as CSS


import Gradual.GUI.Types 

import qualified Data.List as L

pretag :: String
pretag = "<div class='dropdown'><span class='dropbtn'>"


posttag :: Int -> Int -> String -> String 
posttag i j val
  = "</span><div class='dropdown-content' name='select-" ++ show i ++ "-" ++ show j ++ "' id='select-" ++ show i ++ "-" ++ show j ++ "'>"
  ++ "<button type='button' onclick=\"showPrev("++ name ++ ")\"> << </button>" 
  ++ "<div id=" ++ name ++ ">"
  ++ val
  ++ "</div>" 
  ++ "<button type='button' onclick=\"showNext("++ name ++ ")\"> >> </button>" 
  -- ++ "undefined"
  ++ "</div>"
  ++ "</div>"
  where
    name = "'content-" ++ show i ++ "-" ++ show j ++ "'"


tag :: Loc -> [(String, Loc)] -> (Int, Int, SrcSpan, String) -> [(String, Loc)]
tag eof toks (i, j, sp, v) = go False toks 
  where
    go True [] = [("</span>"++ posttag i j v, eof)]
    go _    [] = []
    go b    ((s,l):rest)
      | l `inLoc` sp, not b 
      = (pretag ++ "<span class='"++ sourceName i++ "'>" ++ s , l):go True rest 
      | not (l `inLoc` sp), b 
      = ("</span>"++ posttag i j v ++ s, l):rest 
      | otherwise 
      = (s,l):go b rest 

_highlight :: String -> Loc -> [(String, Loc)] -> SrcSpan -> [(String, Loc)] 
_highlight color eof toks sp = go False toks 
  where
    go True [] = [("</span>", eof)]
    go _    [] = []
    go b    ((s,l):rest)
      | l `inLoc` sp, not b 
      = ("<span id=\"background-color: " ++ color ++ "\">" ++s, l):go True rest 
      | not (l `inLoc` sp), b 
      = ("</span>" ++ s, l):rest 
      | otherwise 
      = (s,l):go b rest 

inLoc :: Loc -> SrcSpan -> Bool 
inLoc l (SS start end) 
  = L (sline, scol) <= l && l <= L (eline, ecol)
  where
    (_,sline, scol) = sourcePosElts start
    (_,eline, ecol) = sourcePosElts end


renderHtml :: FilePath -> String -> LocTokens -> SDeps -> String 
renderHtml html initSrc tokens deps 
  = topAndTail initSrc html $! body
  where 
    eof  = thd3 $ last tokens
    body = formButton 1 $ CSS.pre $ concat $ map fst taggedTokens
    taggedTokens = foldl (tag eof) 
                      [(CSS.renderToken (x, y), z) | (x,y,z) <- tokens] 
                      (srcDeps deps)

formButton :: Int -> String -> String 
formButton i str@(_:_:rest) 
  | L.isPrefixOf "??" str
  = bform i ++ formButton (i+1) rest
formButton i (x:rest)
  = x:formButton i rest
formButton _ []
  = []  



classbuttonName :: Int -> String 
classbuttonName i = "classbutton-" ++ show i 


sourceName :: Int -> String 
sourceName i = "src-" ++ show i 

bform :: Int -> String
bform i = 
  "<button type='button' id='button-" ++ show i ++ 
  "' onclick='gradualClick("++ show i ++ ")'" ++ 
  " class='" ++ classbuttonName i ++ "'>??</button>"


topAndTail :: String -> String -> String -> String
topAndTail initSrc title body = htmlHeader initSrc title ++ body ++ htmlClose


-- ATTENTION: these colors should match with ones in util.js
-- TODO: use spec
colours :: [(Int, String)]
colours = 
  [ (1, "#E59EFF")
  , (2, "#FF9EE9")
  , (3, "#FF9EB8")
  , (4, "#FFB49E")
  , (5, "#FFE59E")
  , (6, "#E9FF9E")]

bottonsCss :: String 
bottonsCss = concatMap bottonCss colours 

bottonCss :: (Int, String) -> String 
bottonCss (i, color)= unlines 
  [ "<style>"
  , "." ++ classbuttonName i ++ "{"
  , "background-color: " ++ color ++ ";"
  , "cursor: pointer;"
  , "type: button;}"
  , ""
  , "." ++ sourceName i ++ "{"
  , "background-color: #f0f0f0;}"
  , "</style>"
  ]

htmlHeader :: String -> String -> String
htmlHeader initSrc title = unlines
  [ "<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 3.2 Final//EN\">"
  , "<html>"
  , "<head>"
  , "<title>" ++ title ++ "</title>"
  , "</head>"
  , "<style type='text/css'>"
  , " form {display:inline; margin:0px; padding:0px; }"
  , "</style>"
  , "<script src='http://goto.ucsd.edu/~nvazou/gradual/util.js'></script>"
  , initSrc
  , "<link type='text/css' rel='stylesheet' href='http://goto.ucsd.edu/~nvazou/gradual/liquid.css' />"
  , bottonsCss
  , "<body>"
  , "<hr>"
  , "Interactive Solution based on Gradual Typing"
  ]

htmlClose :: String
htmlClose  = "\n</body>\n</html>"  