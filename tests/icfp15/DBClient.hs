module DBClient where
import Data.Maybe (catMaybes)
import DataBase

import Prelude hiding (product)

import Control.Applicative ((<$>))

data Tag = Name | PID | Mail | Grade
        deriving (Eq, Show)

data Value = N Name | I Int    
         deriving (Eq, Show)


-- This represents Strings....
-- Signleton Types people do the same hack, as 
-- Strings are not "easy" to express into logic

data Name = Niki | Alex | Ranjit | NMail | AMail | RMail
           deriving (Eq, Show)


{-@ assume N :: x:Name -> {v:Value | v = nn x} @-}
{-@ assume I :: n:Int  -> {v:Value | v = ii n} @-}

{-@ measure nn :: Name -> Value @-}
{-@ measure ii :: Int  -> Value @-}

{-@ type Grades = [GradingScheme] @-}
{-@ type Names = [NameScheme] @-}
{-@ type GradingScheme = {v:Dict <{\t -> GradingDomain t}, {\t v -> GradingRange t v}> Tag Value | ValidGradingScheme v} @-}
{-@ type NameScheme    = {v:Dict <{\t -> t = Name}, {\t v -> t == Name => ValidName v}> Tag Value | ValidNameScheme v} @-}

grades :: [Dict Tag Value]
{-@ grades :: Grades @-}
grades = [gNiki, gAlex, gRanjit]


gNiki, gAlex, gRanjit :: Dict Tag Value
{-@ gNiki, gAlex, gRanjit :: GradingScheme @-}
gNiki   = (Name := N Niki) += (PID := I 123) += (Grade := I 7) += (Mail := N NMail) += empty
gAlex   = mkRow (N Alex)   (I 456) (I 8) (N AMail)
gRanjit = mkRow (N Ranjit) (I 789) (I 9) (N RMail)


mkRow :: Value -> Value -> Value -> Value -> Dict Tag Value
{-@ mkRow :: 
             {name: Value | ValidName  name } 
          -> {pid:  Value | ValidPID   pid  } 
          -> {grade:Value | ValidGrade grade} 
          -> {mail: Value | ValidMail  mail } 
          -> GradingScheme
  @-}
mkRow name pid grade mail  
  = (Grade := grade) += (Mail := mail) += (Name := name) += (PID := pid) += empty


-------------------------------------------------------------------------------
--------------- Some Queries --------------------------------------------------
-------------------------------------------------------------------------------

-- Students With Grade >= n

{-@ query1 :: Grades -> Names @-}
query1 :: [Dict Tag Value] -> [Dict Tag Value]
query1 = map qproject . catMaybes . map qselect

{-@ qselect :: GradingScheme -> Maybe GradingScheme @-}
qselect :: Dict Tag Value -> Maybe (Dict Tag Value)
qselect	 = select (\t v -> if t == Grade then toInt v >= 8 else False)


{-@ qproject :: GradingScheme -> NameScheme @-}
qproject :: Dict Tag Value -> Dict Tag Value 
qproject = project [Name]




-------------------------------------------------------------------------------
--------------- Helpers  ------------------------------------------------------
-------------------------------------------------------------------------------

toInt :: Value -> Int
{-@ toInt :: x:{Value | isInt x} -> {v:Int | v = fromInt x} @-}
toInt (I x) = x

-------------------------------------------------------------------------------
--------------- Some predicates -----------------------------------------------
-------------------------------------------------------------------------------


{-@ predicate ValidGradingScheme V = 
	  ((listElts (dom V) = Set_cup (Set_sng Mail) 
	  	                  (Set_cup (Set_sng Grade) 
	  	                  (Set_cup (Set_sng PID) 
	  	                           (Set_sng Name))))) @-}

{-@ predicate ValidNameScheme V = 
	  (listElts (dom V) = (Set_sng Name)) @-}

{-@ predicate GradingDomain T   = (T = PID || T = Name || T = Grade || T = Mail) @-}

{-@ predicate GradingRange  T V =  (T == PID  => ValidPID   V) 
                                && (T == Name => ValidName  V) 
                                && (T = Grade => ValidGrade V) 
                                && (T = Mail  => ValidMail  V) @-}

{-@ predicate ValidPID   V = isInt V @-}
{-@ predicate ValidName  V = isName V @-}
{-@ predicate ValidGrade V = isInt V  && (0 <= fromInt V) && (fromInt V <= 10)  @-}
{-@ predicate ValidMail  V = isName V @-}



-------------------------------------------------------------------------------
--------------- Some measures -------------------------------------------------
-------------------------------------------------------------------------------


{-@ measure fromInt :: Value -> Int 
    fromInt(I n) = n
  @-}

{-@ measure isInt @-}
isInt :: Value -> Bool
isInt (I _) = True
isInt _     = False

{-@ measure isName @-}
isName :: Value -> Bool
isName (N _) = True
isName _     = False