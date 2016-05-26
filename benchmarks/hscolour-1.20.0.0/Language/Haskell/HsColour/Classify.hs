module Language.Haskell.HsColour.Classify
  ( TokenType(..)
  , tokenise
  ) where

{-@ LIQUID "--totality"     @-}
{-@ LIQUID "--no-eliminate" @-}

import qualified GHC.Read -- LIQUID get lex specification

import Data.Char (isSpace, isUpper, isLower, isDigit)
import Data.List

-- | Lex Haskell source code into an annotated token stream, without
--   discarding any characters or layout.
tokenise :: String -> [(TokenType,String)]
tokenise str = 
    let chunks = glue . chunk $ str 
    in markDefs $ map (\s-> (classify s,s)) chunks

{-@ markDefs :: xs:_ -> _ / [(len xs), 1] @-}
markDefs :: [(TokenType, String)] -> [(TokenType, String)]
markDefs [] = []
markDefs ((Varid, s) : rest) = (Definition, s) : continue rest
markDefs ((Varop, ">") : (Space, " ") : (Varid, d) : rest) =
    (Varop, ">") : (Space, " ") : (Definition, d) : continue rest
markDefs rest = continue rest

{-@ continue :: xs:_ -> _ / [(len xs), 0] @-}
continue rest 
    = let (thisLine, nextLine) = span (/= (Space, "\n")) rest
      in
        case nextLine of
          [] -> thisLine
          ({-(Space, "\n")-}_:nextLine') -> (thisLine ++ ((Space, "\n") : (markDefs nextLine')))


-- Basic Haskell lexing, except we keep whitespace.
chunk :: String -> [String]
chunk []    = []
chunk ('\r':s) = chunk s -- get rid of DOS newline stuff
chunk ('\n':s) = "\n": chunk s
chunk (c:s) | isLinearSpace c
            = (c:ss): chunk rest where (ss,rest) = span isLinearSpace s
chunk ('{':'-':s) = let (com,s') = nestcomment 0 s
                    in ('{':'-':com) : chunk s'
chunk s = case Prelude.lex s of
              []             -> [head s]: chunk (tail s) -- e.g. inside comment
              ((tok@('-':'-':_),rest):_)
                  | all (=='-') tok -> (tok++com): chunk s'
                                       where (com,s') = eolcomment rest
              ((tok,rest):_) -> tok: chunk rest

isLinearSpace c = c `elem` " \t\f" -- " \t\xa0"

-- Glue sequences of tokens into more useful blobs
--glue (q:".":n:rest) | Char.isUpper (head q)	-- qualified names
--                    = glue ((q++"."++n): rest)
glue ("`":rest) =				-- `varid` -> varop
  case glue rest of
    (qn:"`":rest) -> ("`"++qn++"`"): glue rest
    _             -> "`": glue rest
glue (s:ss)       | all (=='-') s && length s >=2	-- eol comment
                  = (s++concat c): glue rest
                  where (c,rest) = break ('\n'`elem`) ss
--glue ("{":"-":ss)  = ("{-"++c): glue rest	-- nested comment
--                  where (c,rest) = nestcomment 0 ss
glue ("(":ss) = case rest of
                ")":rest -> ("(" ++ concat tuple ++ ")") : glue rest
                _         -> "(" : glue ss
              where (tuple,rest) = span (==",") ss
glue ("[":"]":ss) = "[]" : glue ss
glue ("\n":"#":ss)= "\n" : ('#':concat line) : glue rest
                  where (line,rest) = break ('\n'`elem`) ss
glue (s:ss)       = s: glue ss
glue []           = []

-- Deal with comments.
{-@ Decrease nestcomment 2 @-}

{-@ nestcomment :: Nat -> xs:_ -> (_,{v:_|(if ((len xs) = 0) then ((len v) = 0) else ((len v) <= (len xs))) }) @-}

nestcomment :: Int -> String -> (String,String)
nestcomment n ('{':'-':ss) | n>=0 = (("{-"++cs),rm)
                                  where (cs,rm) = nestcomment (n+1) ss
nestcomment n ('-':'}':ss) | n>0  = let (cs,rm) = nestcomment (n-1) ss
                                    in (("-}"++cs),rm)
nestcomment n ('-':'}':ss) | n==0 = ("-}",ss)
nestcomment n (s:ss)       | n>=0 = ((s:cs),rm)
                                  where (cs,rm) = nestcomment n ss
nestcomment n [] = ([],[])


{-@ eolcomment :: xs:_ -> ({v:_ | (len v) <= (len xs)},{v:_ | (len v) <= (len xs)}) @-}
eolcomment :: String -> (String,String)
eolcomment s@('\n':_) = ([], s)
eolcomment ('\r':s)   = eolcomment s
eolcomment (c:s)      = (c:cs, s') where (cs,s') = eolcomment s
eolcomment []         = ([],[])

-- | Classification of tokens as lexical entities
data TokenType =
  Space | Keyword | Keyglyph | Layout | Comment | Conid | Varid |
  Conop | Varop   | String   | Char   | Number  | Cpp   | Error |
  Definition
  deriving (Eq,Show)

classify :: String -> TokenType
classify s@(h:t)
    | isSpace h              = Space
    | all (=='-') s          = Comment
    | "--" `isPrefixOf` s
      && any isSpace s       = Comment		-- not fully correct
    | "{-" `isPrefixOf` s    = Comment
    | s `elem` keywords      = Keyword
    | s `elem` keyglyphs     = Keyglyph
    | s `elem` layoutchars   = Layout
    | isUpper h              = Conid
    | s == "[]"              = Conid
    | h == '(' && isTupleTail t = Conid
    | h == '#'               = Cpp
    | isLower h              = Varid
    | h `elem` symbols       = Varop
    | h==':'                 = Conop
    | h=='`'                 = Varop
    | h=='"'                 = String
    | h=='\''                = Char
    | isDigit h              = Number
    | otherwise              = Error
classify _ = Space

isTupleTail [')'] = True
isTupleTail (',':xs) = isTupleTail xs
isTupleTail _ = False


-- Haskell keywords
keywords =
  ["case","class","data","default","deriving","do","else","forall"
  ,"if","import","in","infix","infixl","infixr","instance","let","module"
  ,"newtype","of","qualified","then","type","where","_"
  ,"foreign","ccall","as","safe","unsafe"]
keyglyphs =
  ["..","::","=","\\","|","<-","->","@","~","=>","[","]"]
layoutchars =
  map (:[]) ";{}(),"
symbols =
  "!#$%&*+./<=>?@\\^|-~"
