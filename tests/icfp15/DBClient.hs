module DBClient where

import DataBase

import Prelude hiding (product)

data Tag = Name | PID | Mail | Grade
        deriving Eq

data Value = N Name | I Int    
         deriving Eq


-- This represents Strings....
-- Signleton Types people do the same hack, as 
-- Strings are not "easy" to express into logic

data Name = Niki | Alex | Ranjit | NMail | AMail | RMail
           deriving Eq


{-@ assume N :: x:Name -> {v:Value | v = N x} @-}
{-@ assume I :: n:Int  -> {v:Value | v = I n} @-}


{-@ type Grades = [GradingScheme] @-}
{-@ type GradingScheme = {v:Dict <{\t -> GradingDomain t}, {\t v -> GradingRange t v}> Tag Value | ValidGradingScheme v} @-}

grades :: [Dict Tag Value]
{-@ grades :: Grades @-}
grades = [gNiki, gAlex, gRanjit]


gNiki, gAlex, gRanjit :: Dict Tag Value
{-@ gNiki, gAlex, gRanjit :: GradingScheme @-}
gNiki   = (Name := N Niki) += (PID := I 123) += (Grade := I 9) += (Mail := N NMail) += empty
gAlex   = mkRow (N Alex)   (I 456) (I 9) (N AMail)
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
--------------- Some predicates -----------------------------------------------
-------------------------------------------------------------------------------


{-@ predicate ValidGradingScheme V = 
	  ((listElts (dom V) = Set_cup (Set_sng Mail) 
	  	                  (Set_cup (Set_sng Grade) 
	  	                  (Set_cup (Set_sng PID) 
	  	                           (Set_sng Name))))) @-}

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