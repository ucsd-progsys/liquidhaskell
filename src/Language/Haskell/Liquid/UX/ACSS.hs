{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

-- | Formats Haskell source code as HTML with CSS and Mouseover Type Annotations
module Language.Haskell.Liquid.UX.ACSS (
    hscolour
  , hsannot
  , AnnMap (..)
  , breakS
  , srcModuleName
  , Status (..)
  , tokeniseWithLoc
  ) where

import Prelude hiding (error)
import qualified Liquid.GHC.API as SrcLoc

import Language.Haskell.HsColour.Anchors
import Language.Haskell.HsColour.Classify as Classify
import Language.Haskell.HsColour.HTML (renderAnchors, escape)
import qualified Language.Haskell.HsColour.CSS as CSS

import Data.Either (partitionEithers)
import Data.Maybe  (fromMaybe)
import qualified Data.HashMap.Strict as M
import Data.List   (find, isPrefixOf, findIndex, elemIndices, intercalate, elemIndex)
import Data.Char   (isSpace)
import Text.Printf
import Liquid.GHC.Misc
import Language.Haskell.Liquid.Types.Errors (panic, impossible)

data AnnMap  = Ann
  { types   :: M.HashMap Loc (String, String) -- ^ Loc -> (Var, Type)
  , errors  :: [(Loc, Loc, String)]           -- ^ List of error intervals
  , status  :: !Status
  , sptypes :: ![(SrcLoc.RealSrcSpan, (String, String)) ]-- ^ Type information with spans
  }

data Status = Safe | Unsafe | Error | Crash
              deriving (Eq, Ord, Show)

data Annotation = A {
    typ :: Maybe String         -- ^ type  string
  , err :: Maybe String         -- ^ error string
  , lin :: Maybe (Int, Int)     -- ^ line number, total width of lines i.e. max (length (show lineNum))
  } deriving (Show)


-- | Formats Haskell source code using HTML and mouse-over annotations
hscolour :: Bool     -- ^ Whether to include anchors.
         -> Bool     -- ^ Whether input document is literate haskell or not
         -> String   -- ^ Haskell source code, Annotations as comments at end
         -> String   -- ^ Coloured Haskell source code.

hscolour anchor lhs = hsannot anchor Nothing lhs . splitSrcAndAnns

type CommentTransform = Maybe (String -> [(TokenType, String)])

-- | Formats Haskell source code using HTML and mouse-over annotations
hsannot  :: Bool             -- ^ Whether to include anchors.
         -> CommentTransform -- ^ Function to refine comment tokens
         -> Bool             -- ^ Whether input document is literate haskell or not
         -> (String, AnnMap) -- ^ Haskell Source, Annotations
         -> String           -- ^ Coloured Haskell source code.

hsannot anchor tx False z     = hsannot' Nothing anchor tx z
hsannot anchor tx True (s, m) = concatMap chunk $ litSpans $ joinL $ classify $ inlines s
  where chunk (Code c, l)     = hsannot' (Just l) anchor tx (c, m)
        chunk (Lit c , _)     = c

litSpans :: [Lit] -> [(Lit, Loc)]
litSpans lits = zip lits $ spans lits
  where spans = tokenSpans Nothing . map unL

hsannot' :: Maybe Loc
         -> Bool -> CommentTransform -> (String, AnnMap) -> String
hsannot' baseLoc anchor tx =
    CSS.pre
    . (if anchor then concatMap (renderAnchors renderAnnotToken)
                      . insertAnnotAnchors
                 else concatMap renderAnnotToken)
    . annotTokenise baseLoc tx

tokeniseWithLoc :: CommentTransform -> String -> [(TokenType, String, Loc)]
tokeniseWithLoc tx str = zipWith (\(x,y) z -> (x, y, z)) toks spans
  where
    toks       = tokeniseWithCommentTransform tx str
    spans      = tokenSpans Nothing $ map snd toks

-- | annotTokenise is absurdly slow: O(#tokens x #errors)

annotTokenise :: Maybe Loc -> CommentTransform -> (String, AnnMap) -> [(TokenType, String, Annotation)]
annotTokenise baseLoc tx (src, annm) = zipWith (\(x,y) z -> (x,y,z)) toks annots
  where
    toks       = tokeniseWithCommentTransform tx src
    spans      = tokenSpans baseLoc $ map snd toks
    annots     = fmap (spanAnnot linWidth annm) spans
    linWidth   = length $ show $ length $ lines src

spanAnnot :: Int -> AnnMap -> Loc -> Annotation
spanAnnot w (Ann ts es _ _) loc = A t e b
  where
    t = fmap snd (M.lookup loc ts)
    e = "ERROR" <$ find (loc `inRange`) [(x,y) | (x,y,_) <- es]
    b = spanLine w loc

spanLine :: t -> Loc -> Maybe (Int, t)
spanLine w (L (l, c))
  | c == 1    = Just (l, w)
  | otherwise = Nothing

inRange :: Loc -> (Loc, Loc) -> Bool
inRange (L (l0, c0)) (L (l, c), L (l', c'))
  = l <= l0 && c <= c0 && l0 <= l' && c0 < c'

tokeniseWithCommentTransform :: Maybe (String -> [(TokenType, String)]) -> String -> [(TokenType, String)]
tokeniseWithCommentTransform Nothing  = tokenise
tokeniseWithCommentTransform (Just g) = concatMap (expand g) . tokenise
  where expand f (Comment, s) = f s
        expand _ z            = [z]

tokenSpans :: Maybe Loc -> [String] -> [Loc]
tokenSpans = scanl plusLoc . fromMaybe (L (1, 1))

plusLoc :: Loc -> String -> Loc
plusLoc (L (l, c)) s
  = case '\n' `elemIndices` s of
      [] -> L (l, c + n)
      is -> L (l + length is, n - maximum is)
    where n = length s

renderAnnotToken :: (TokenType, String, Annotation) -> String
renderAnnotToken (x, y, a)  = renderLinAnnot (lin a)
                            $ renderErrAnnot (err a)
                            $ renderTypAnnot (typ a)
                            $ CSS.renderToken (x, y)



renderTypAnnot :: (PrintfArg t, PrintfType t) => Maybe String -> t -> t
renderTypAnnot (Just ann) s = printf "<a class=annot href=\"#\"><span class=annottext>%s</span>%s</a>" (escape ann) s
renderTypAnnot Nothing    s = s

renderErrAnnot :: (PrintfArg t1, PrintfType t1) => Maybe t -> t1 -> t1
renderErrAnnot (Just _) s   = printf "<span class=hs-error>%s</span>" s
renderErrAnnot Nothing  s   = s

renderLinAnnot :: (Show t, PrintfArg t1, PrintfType t1)
               => Maybe (t, Int) -> t1 -> t1
renderLinAnnot (Just d) s   = printf "<span class=hs-linenum>%s: </span>%s" (lineString d) s
renderLinAnnot Nothing  s   = s

lineString :: Show t => (t, Int) -> [Char]
lineString (i, w) = replicate (w - length is) ' ' ++ is
  where is        = show i

{- Example Annotation:
<a class=annot href="#"><span class=annottext>x#agV:Int -&gt; {VV_int:Int | (0 &lt;= VV_int),(x#agV &lt;= VV_int)}</span>
<span class='hs-definition'>NOWTRYTHIS</span></a>
-}


insertAnnotAnchors :: [(TokenType, String, a)] -> [Either String (TokenType, String, a)]
insertAnnotAnchors toks
  = stitch (zip toks' toks) $ insertAnchors toks'
  where toks' = [(x,y) | (x,y,_) <- toks]

stitch ::  Eq b => [(b, c)] -> [Either a b] -> [Either a c]
stitch xys ((Left a) : rest)
  = Left a : stitch xys rest
stitch ((x,y):xys) ((Right x'):rest)
  | x == x'
  = Right y : stitch xys rest
  | otherwise
  = panic Nothing "stitch"
stitch _ []
  = []
stitch _ _
  = impossible Nothing "stitch: cannot happen"

splitSrcAndAnns ::  String -> (String, AnnMap)
splitSrcAndAnns s =
  let ls = lines s in
  case elemIndex breakS ls of
    Nothing -> (s, Ann M.empty [] Safe mempty)
    Just i  -> (src, ann)
               where (codes, _:mname:annots) = splitAt i ls
                     ann   = annotParse mname $ dropWhile isSpace $ unlines annots
                     src   = unlines codes

srcModuleName :: String -> String
srcModuleName = fromMaybe "Main" . tokenModule . tokenise

tokenModule :: [(TokenType, [Char])] -> Maybe [Char]
tokenModule toks
  = do i <- elemIndex (Keyword, "module") toks
       let (_, toks')  = splitAt (i+2) toks
       j <- findIndex ((Space ==) . fst) toks'
       let (toks'', _) = splitAt j toks'
       return $ concatMap snd toks''

breakS :: [Char]
breakS = "MOUSEOVER ANNOTATIONS"

annotParse :: String -> String -> AnnMap
annotParse mname s = Ann (M.fromList ts) [(x,y,"") | (x,y) <- es] Safe mempty
  where
    (ts, es)       = partitionEithers $ parseLines mname 0 $ lines s


parseLines :: [Char]
           -> Int
           -> [[Char]]
           -> [Either (Loc, ([Char], [Char])) (Loc, Loc)]
parseLines _ _ []
  = []

parseLines mname i ("":ls)
  = parseLines mname (i+1) ls

parseLines mname i (_:_:l:c:"0":l':c':rest')
  = Right (L (line, col), L (line', col')) : parseLines mname (i + 7) rest'
    where line  = read l  :: Int
          col   = read c  :: Int
          line' = read l' :: Int
          col'  = read c' :: Int

parseLines mname i (x:f:l:c:n:rest)
  | f /= mname
  = parseLines mname (i + 5 + num) rest'
  | otherwise
  = Left (L (line, col), (x, anns)) : parseLines mname (i + 5 + num) rest'
    where line  = read l :: Int
          col   = read c :: Int
          num   = read n :: Int
          anns  = intercalate "\n" $ take num rest
          rest' = drop num rest

parseLines _ i _
  = panic Nothing $ "Error Parsing Annot Input on Line: " ++ show i

instance Show AnnMap where
  show (Ann ts es _ _) =  "\n\n"
                      ++ concatMap ppAnnotTyp (M.toList ts)
                      ++ concatMap ppAnnotErr [(x,y) | (x,y,_) <- es]

ppAnnotTyp :: (PrintfArg t, PrintfType t1) => (Loc, (t, String)) -> t1
ppAnnotTyp (L (l, c), (x, s))     = printf "%s\n%d\n%d\n%d\n%s\n\n\n" x l c (length $ lines s) s

ppAnnotErr :: PrintfType t => (Loc, Loc) -> t
ppAnnotErr (L (l, c), L (l', c')) = printf " \n%d\n%d\n0\n%d\n%d\n\n\n\n" l c l' c'


---------------------------------------------------------------------------------
---- Code for Dealing With LHS, stolen from Language.Haskell.HsColour.HsColour --
---------------------------------------------------------------------------------

-- | Separating literate files into code\/comment chunks.
data Lit = Code {unL :: String} | Lit {unL :: String} deriving (Show)

-- Re-implementation of 'lines', for better efficiency (but decreased laziness).
-- Also, importantly, accepts non-standard DOS and Mac line ending characters.
-- And retains the trailing '\n' character in each resultant string.
inlines :: String -> [String]
inlines str = lines' str id
  where
  lines' []             acc = [acc []]
  lines' ('\^M':'\n':s) acc = acc ['\n'] : lines' s id  -- DOS
  lines' ('\n':s)       acc = acc ['\n'] : lines' s id  -- Unix
  lines' (c:s)          acc = lines' s (acc . (c:))


-- | The code for classify is largely stolen from Language.Preprocessor.Unlit.
classify ::  [String] -> [Lit]
classify []             = []
classify (x:xs) | "\\begin{code}"`isPrefixOf`x
                        = Lit x: allProg "code" xs
classify (x:xs) | "\\begin{spec}"`isPrefixOf`x
                        = Lit x: allProg "spec" xs
classify (('>':x):xs)   = Code ('>':x) : classify xs
classify (x:xs)         = Lit x: classify xs


allProg :: [Char] -> [[Char]] -> [Lit]
allProg name  = go
  where
    end       = "\\end{" ++ name ++ "}"
    go []     = []  -- Should give an error message,
                    -- but I have no good position information.
    go (x:xs) | end `isPrefixOf `x
              = Lit x: classify xs
    go (x:xs) = Code x: go xs


-- | Join up chunks of code\/comment that are next to each other.
joinL :: [Lit] -> [Lit]
joinL []                  = []
joinL (Code c:Code c2:xs) = joinL (Code (c++c2):xs)
joinL (Lit c :Lit c2 :xs) = joinL (Lit  (c++c2):xs)
joinL (lit:xs)            = lit: joinL xs
