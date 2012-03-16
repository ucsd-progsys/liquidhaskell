{-# LANGUAGE NoMonomorphismRestriction, FlexibleInstances, UndecidableInstances, TypeSynonymInstances, TupleSections #-}

module Language.Haskell.Liquid.Parse 
( 
    Inputable (..)
) 
where

import GHC
import TypeRep
import TysWiredIn   (intTyCon, boolTyCon)
import Control.Monad
import Text.Parsec
import Text.Parsec.Expr
import Text.Parsec.Language
import Text.Parsec.String
import qualified Text.Parsec.Token as Token
import Control.Applicative ((<$>), (<*))
import qualified Data.Map as M
import Data.Char (isLower)
import Data.List (intercalate)
import Language.Haskell.Liquid.Misc
import Language.Haskell.Liquid.Fixpoint
import Language.Haskell.Liquid.RefType
import qualified Language.Haskell.Liquid.Measure as Measure
import Language.Haskell.Liquid.Bare

--------------------------------------------------------------------

languageDef =
  emptyDef { Token.commentStart    = "/*"
           , Token.commentEnd      = "*/"
           , Token.commentLine     = "//"
           , Token.identStart      = satisfy (\_ -> False) -- letter 
           , Token.identLetter     = satisfy (\_ -> False) -- satisfy (`elem` symChars)
           , Token.reservedNames   = [ "SAT"
                                     , "UNSAT"
                                     , "true"
                                     , "false"
                                     , "mod"
                                     , "Bexp"
                                     , "forall"
                                     , "assume"
                                     , "measure"
                                     , "module"
                                     , "spec"
                                     , "where"
                                     , "import"
                                     , "_|_"
                                     , "|"
                                     ]
           , Token.reservedOpNames = [ "+", "-", "*", "/" 
                                     , "<", ">", "<=", ">=", "=", "!="
                                     , "mod", "and", "or" 
                                   --, "is"
                                     , "&&", "||"
                                     , "~", "=>", "<=>"
                                     , "->"
                                     , ":="
                                     , "?", "Bexp" -- , "'"
                                     ]
           }

lexer      = Token.makeTokenParser languageDef
reserved   = Token.reserved   lexer
reservedOp = Token.reservedOp lexer
parens     = Token.parens     lexer
brackets   = Token.brackets   lexer
braces     = Token.braces     lexer
semi       = Token.semi       lexer
comma      = Token.comma      lexer
colon      = Token.colon      lexer
dot        = Token.dot        lexer
whiteSpace = Token.whiteSpace lexer
identifier = Token.identifier lexer

blanks  = many (satisfy (`elem` [' ', '\t']))

integer =   try (liftM toInt is) 
       <|>  liftM (negate . toInt) (char '-' >> is)
  where is      = liftM2 (\is _ -> is) (many1 digit) blanks 
        toInt s = (read s) :: Integer 

----------------------------------------------------------------
------------------------- Expressions --------------------------
----------------------------------------------------------------

condIdP  :: [Char] -> (String -> Bool) -> Parser String
condIdP chars f 
  = do c  <- letter
       cs <- many (satisfy (`elem` chars))
       blanks
       let s = c:cs
       if f (c:cs) then return (c:cs) else parserZero

tyVarIdP :: Parser String
tyVarIdP = condIdP alphanums (isLower . head) 
  where alphanums = ['a'..'z'] ++ ['0'..'9']

lowerIdP :: Parser String
lowerIdP = condIdP symChars (isLower . head)

upperIdP :: Parser String
upperIdP = condIdP symChars (not . isLower . head)

symbolP :: Parser Symbol
symbolP = liftM stringSymbol symCharsP 


constantP :: Parser Constant
constantP = liftM I integer

exprP :: Parser Expr 
exprP =  expr2P <|> lexprP

lexprP :: Parser Expr 
lexprP   
  =  (try $ parens exprP)
 <|> (try $ parens cexprP)
 <|> (try exprfP)
 <|> (try (liftM ((`EDat` FObj) . stringSymbol) upperIdP))
 <|> liftM EVar symbolP
 <|> liftM ECon constantP
 <|> (reserved "_|_" >> return EBot)



exprfP        = liftM2 EApp symbolP argsP
  where argsP = try (parens $ brackets esP) <|> parens esP
        esP   = sepBy exprP comma 

expr2P = buildExpressionParser bops lexprP

bops = [ [Infix  (reservedOp "*"   >> return (EBin Times)) AssocLeft]
       , [Infix  (reservedOp "/"   >> return (EBin Div  )) AssocLeft]
       , [Infix  (reservedOp "+"   >> return (EBin Plus )) AssocLeft]
       , [Infix  (reservedOp "-"   >> return (EBin Minus)) AssocLeft]
       , [Infix  (reservedOp "mod" >> return (EBin Mod  )) AssocLeft]
       ]

cexprP 
  = do e  <- exprP 
       colon >> colon
       so <- sortP
       return $ ECst e so

sortP
  =   try (string "Integer" >> return FInt)
  <|> try (string "Int"     >> return FInt)
  <|> try (string "Bool"    >> return FBool)
  <|> (symCharsP >>= return . FPtr . FLoc . stringSymbol) 


symCharsP = (condIdP symChars (\_ -> True))

---------------------------------------------------------------------
-------------------------- Predicates -------------------------------
---------------------------------------------------------------------

qmP = reserved "?" <|> reserved "Bexp"

predP :: Parser Pred
predP =  parens pred2P
     <|> (qmP >> liftM PBexp exprP)
     <|> (reserved "true"  >> return PTrue)
     <|> (reserved "false" >> return PFalse)
     <|> (try predrP)
     <|> (try (liftM PBexp exprfP))

pred2P = buildExpressionParser lops predP 

lops = [ [Prefix (reservedOp "~"   >> return PNot)]
       , [Infix  (reservedOp "&&"  >> return (\x y -> PAnd [x,y])) AssocRight]
       , [Infix  (reservedOp "||"  >> return (\x y -> POr  [x,y])) AssocRight]
       , [Infix  (reservedOp "=>"  >> return PImp) AssocRight]
       , [Infix  (reservedOp "<=>" >> return PIff) AssocRight]]
       
predrP = do e1    <- expr2P
            r     <- brelP
            e2    <- expr2P 
            return $ r e1 e2

brelP ::  Parser (Expr -> Expr -> Pred)
brelP =  (reservedOp "="  >> return (PAtom Eq))
     <|> (reservedOp "!=" >> return (PAtom Ne))
     <|> (reservedOp "<"  >> return (PAtom Lt))
     <|> (reservedOp "<=" >> return (PAtom Le))
     <|> (reservedOp ">"  >> return (PAtom Gt))
     <|> (reservedOp ">=" >> return (PAtom Ge))
     -- <|> (reservedOp "is" >> return (hasTag  )) 

----------------------------------------------------------------------------------------
------------------------------------ BareTypes -----------------------------------------
----------------------------------------------------------------------------------------


bareTypeP   
  =  try bareFunP
 <|> bareAllP
 <|> bareAtomP 
 
bareArgP 
  =  bareAtomP  
 <|> parens bareTypeP

bareAtomP 
  =  refP bbaseP 
 <|> try (dummyP bbaseP)

bbaseP 
  =  liftM BLst (brackets bareTypeP)
 <|> liftM mkTup (parens $ sepBy bareTypeP comma)
 <|> try (liftM2 BCon upperIdP (sepBy bareTypeP blanks))
 <|> try (liftM (`BCon` []) upperIdP)
 <|> liftM BVar lowerIdP

mkTup [x] _ = x
mkTup xs  r = BTup xs r

bareAllP 
  = do reserved "forall"
       as <- sepBy1 tyVarIdP comma
       dot
       t  <- bareTypeP
       return $ tr_foldr' BAll t as
       -- return $ foldl' (\t a -> BAll a t) t (rev as)

data ArrowSym = ArrowFun | ArrowPred

arrowP
  =   (reserved "->" >> return ArrowFun)
  <|> (reserved "=>" >> return ArrowPred)

bareFun2P
  = do t1 <- bareArgP 
       a  <- arrowP
       t2 <- bareTypeP
       return $ bareArrow "" t1 a t2 

dummyName pos = "dummy_" ++ name ++ ['@'] ++ line ++ [','] ++ colum
  where name  = sourceName pos
        line  = show $ sourceLine pos  
        colum = show $ sourceColumn pos  

bareFunP  
  = do x  <- try bindP <|> do {p <- getPosition; return $ dummyName p}  
       t1 <- bareArgP 
       a  <- arrowP
       t2 <- bareTypeP
       return $ bareArrow x t1 a t2 

bareArrow x t1 ArrowFun t2
  = BFun x t1 t2
bareArrow x t1 ArrowPred t2
  = foldr (BFun "") t2 (getClasses t1)
   
getClasses (BTup ts _) 
  = getClass <$> ts 
getClasses t 
  = [getClass t]
getClass (BCon c ts _)
  = BClass c ts
getClass t
  = errorstar $ "Cannot convert " ++ (show t) ++ " to Class"

bindP = lowerIdP <* colon

--bindP 
--  = do x <- lowerIdP
--       colon
--       return x

dummyP fm 
  = fm `ap` return (Reft (dummySymbol, []))

refP kindP 
  = braces $ do
      v   <- symbolP 
      colon
      t   <- kindP
      reserved "|"
      ras <- refasP 
      return $ t (Reft (v, ras))

refasP :: Parser [Refa]
refasP  =  (try (brackets $ sepBy (RConc <$> predP) semi)) 
       <|> liftM ((:[]) . RConc) predP

------------------------------------------------------------------
--------------------------- Measures -----------------------------
------------------------------------------------------------------

data Pspec ty bndr 
  = Meas (Measure.Measure ty bndr) 
  | Assm (bndr, ty) 
  | Impt Symbol

specificationP 
  = do reserved "module"
       reserved "spec"
       name  <- symbolP
       reserved "where"
       xs    <- grabs (liftM2 const specP whiteSpace)
       let ms = [m | Meas m <- xs]
       let as = [a | Assm a <- xs]
       let is = [i | Impt i <- xs]
       return $ Measure.qualifySpec name $ Measure.Spec ms as is 

specP 
  = try (reserved "assume"  >> liftM Assm tyBindP)
    <|> (reserved "measure" >> liftM Meas measureP) 
    <|> (reserved "import"  >> liftM Impt symbolP)

tyBindP :: Parser (Symbol, BareType)
tyBindP 
  = do name  <- binderP 
       colon >> colon
       ty    <- bareTypeP
       return (name, ty)

measureP :: Parser (Measure.Measure BareType Symbol)
measureP 
  = do --name  <- binderP 
       --colon >> colon
       --ty    <- bareTypeP
       (x, ty) <- tyBindP  
       whiteSpace
       eqns    <- grabs $ measureDefP $ tyBodyP ty
       return   $ Measure.mkM x ty eqns   

tyBodyP :: BareType -> Parser Measure.Body
tyBodyP ty 
  = case outTy ty of
      Just (BCon "Bool"[] _) -> Measure.P <$> predP 
      _                      -> Measure.E <$> exprP
    where outTy (BAll _ t)   = outTy t
          outTy (BFun _ _ t) = Just t
          outTy _            = Nothing


binderP :: Parser Symbol
binderP =  try symbolP 
       <|> liftM pwr (parens $ many1 (satisfy $ not . (`elem` "()")))
       where pwr s = stringSymbol $ "(" ++ s ++ ")" 


grabs p = try (liftM2 (:) p (grabs p)) 
       <|> return []

measureDefP :: Parser Measure.Body -> Parser (Measure.Def Symbol)
measureDefP bodyP
  = do mname   <- symbolP
       (c, xs) <- parens $ measurePatP
       whiteSpace >> reservedOp "=" >> whiteSpace
       body    <- bodyP 
       whiteSpace
       return   $ Measure.Def mname (stringSymbol c) (stringSymbol <$> xs) body


--measureDefP :: Parser (Measure.Def Symbol)
--measureDefP 
--  = do mname   <- symbolP
--       (c, xs) <- parens $ measurePatP
--       whiteSpace >> reservedOp "=" >> whiteSpace
--       body    <- Measure.E <$> exprP
--       whiteSpace
--       return   $ Measure.Def mname (S c) (S <$> xs) body

measurePatP :: Parser (String, [String])
measurePatP
  =  try (liftM2 (,)   upperIdP (sepBy lowerIdP whiteSpace))
 <|> try (liftM3 (\x c y -> (c, [x,y])) lowerIdP colon lowerIdP)
 <|> (brackets whiteSpace  >> return ("[]",[])) 

{- len (Cons x1 x2 ...) = e -}

----------------------------------------------------------------------------------------
------------------------------- Interacting with Fixpoint ------------------------------
----------------------------------------------------------------------------------------

fixResultP :: Parser a -> Parser (FixResult a)
fixResultP pp 
  =  (reserved "SAT"   >> return Safe)
 <|> (reserved "UNSAT" >> Unsafe <$> (brackets $ sepBy pp comma))  
 <|> (reserved "CRASH" >> crashP pp)

crashP pp
  = do i   <- pp
       msg <- many anyChar
       return $ Crash [i] msg

predSolP 
  = parens $ (predP  <* (comma >> iQualP)) 
    
--iQualP 
--  = upperIdP >> many bracketsWithStuffP
--
--bracketsWithStuffP
--  = (brackets $ many (satisfy $ not . (`elem` "[]"))) >> return ()

iQualP
  = upperIdP >> (parens $ sepBy symbolP comma)

solution1P
  = do reserved "solution:" 
       k  <- symbolP 
       reserved ":=" 
       ps <- brackets $ sepBy predSolP semi
       return (k, simplify $ PAnd ps)

solutionP 
  = M.fromList <$> sepBy solution1P whiteSpace

solutionFileP 
  = liftM2 (,) (fixResultP integer) solutionP

------------------------------------------------------------------------

remainderP p  
  = do res <- p
       str <- stateInput <$> getParserState
       return (res, str) 

doParse p = doParse' p ""

doParse' parser f s
  = case parse (remainderP p) f s of
      Left e         -> errorstar $ "parseError when parsing " ++ s ++ " : " ++ show e
      Right (r, "")  -> r
      Right (r, rem) -> errorstar $ "doParse has leftover when parsing: " ++ rem
  where p = whiteSpace >> parser

----------------------------------------------------------------------------------------
------------------------ Bundling Parsers into a Typeclass -----------------------------
----------------------------------------------------------------------------------------

class Inputable a where
  rr  :: String -> a
  rr' :: String -> String -> a
  rr' = \s -> rr
  rr  = rr' "" 


instance Inputable Symbol where
  rr' = doParse' symbolP

instance Inputable Constant where
  rr' = doParse' constantP 

instance Inputable Pred where
  rr' = doParse' predP 

instance Inputable Expr where
  rr' = doParse' exprP 

instance Inputable [Refa] where
  rr' = doParse' refasP

instance Inputable (FixResult Integer) where
  rr' = doParse' $ fixResultP integer

instance Inputable (FixResult Integer, FixSolution) where
  rr' = doParse' solutionFileP 

instance Inputable BareType where
  rr' = doParse' bareTypeP 

instance Inputable (Measure.Measure BareType Symbol) where
  rr' = doParse' measureP

instance Inputable (Measure.Spec BareType Symbol) where
  rr' = doParse' specificationP




---------------------------------------------------------------
--------------------------- Testing ---------------------------
---------------------------------------------------------------

sa  = "0"
sb  = "x"
sc  = "(x0 + y0 + z0) "
sd  = "(x+ y * 1)"
se  = "_|_ "
sf  = "(1 + x + _|_)"
sg  = "f(x,y,z)"
sh  = "(f((x+1), (y * a * b - 1), _|_))"
si  = "(2 + f((x+1), (y * a * b - 1), _|_))"

s0  = "true"
s1  = "false"
s2  = "v > 0"
s3  = "(0 < v && v < 100)"
s4  = "(x < v && v < y+10 && v < z)"
s6  = "[(v > 0)]"
s6' = "x"
s7' = "(x <=> y)"
s8' = "(x <=> a = b)"
s9' = "(x <=> (a <= b && b < c))"

s7  = "{ v: Int | [(v > 0)] }"
s8  = "x:{ v: Int | v > 0 } -> {v : Int | v >= x}"
s9  = "v = x+y"
s10 = "{v: Int | v = x + y}"

s11 = "x:{v:Int | true } -> {v:Int | true }" 
s12 = "y : {v:Int | true } -> {v:Int | v = x }"
s13 = "x:{v:Int | true } -> y:{v:Int | true} -> {v:Int | v = x + y}"
s14 = "x:{v:a  | true} -> y:{v:b | true } -> {v:a | (x < v && v < y) }"
s15 = "x:Int -> Bool"
s16 = "x:Int -> y:Int -> {v:Int | v = x + y}"
s17 = "a"
s18 = "x:a -> Bool"
s20 = "forall a . x:Int -> Bool"

s21 = "x:{v : GHC.Prim.Int# | true } -> {v : Int | true }" 

r0  = (rr s0) :: Pred
r0' = (rr s0) :: [Refa]
r1  = (rr s1) :: [Refa]


e1, e2  :: Expr  
e1  = rr "(k_1 + k_2)"
e2  = rr "k_1" 

o1, o2, o3 :: FixResult Integer
o1  = rr "SAT " 
o2  = rr "UNSAT [1, 2, 9,10]"
o3  = rr "UNSAT []" 

-- sol1 = doParse solution1P "solution: k_5 := [0 <= VV_int]"
-- sol2 = doParse solution1P "solution: k_4 := [(0 <= VV_int)]" 

b0, b1, b2, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13 :: BareType
b0  = rr "Int"
b1  = rr "x:{v:Int | true } -> y:{v:Int | true} -> {v:Int | v = x + y}"
b2  = rr "x:{v:Int | true } -> y:{v:Int | true} -> {v:Int | v = x - y}"
b4  = rr "forall a . x : a -> Bool"
b5  = rr "Int -> Int -> Int"
b6  = rr "(Int -> Int) -> Int"
b7  = rr "({v: Int | v > 10} -> Int) -> Int"
b8  = rr "(x:Int -> {v: Int | v > x}) -> {v: Int | v > 10}"
b9  = rr "x:Int -> {v: Int | v > x} -> {v: Int | v > 10}"
b10 = rr "[Int]"
b11 = rr "x:[Int] -> {v: Int | v > 10}"
b12 = rr "[Int] -> String"
b13 = rr "x:(Int, [Bool]) -> [(String, String)]"

-- b3 :: BareType
-- b3  = rr "x:Int -> y:Int -> {v:Bool | ((v is True) <=> x = y)}"

m1 = ["len :: [a] -> Int", "len (Nil) = 0", "len (Cons x xs) = 1 + len(xs)"]
m2 = ["tog :: LL a -> Int", "tog (Nil) = 100", "tog (Cons y ys) = 200"]

me1, me2 :: Measure.Measure BareType Symbol 
me1 = (rr $ intercalate "\n" m1) 
me2 = (rr $ intercalate "\n" m2)

