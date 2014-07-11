
{-# LANGUAGE OverloadedStrings         #-}

module Language.Haskell.Liquid.Errors (applySolution) where

import Data.Monoid                              hiding ((<>))
import Control.Exception                        (Exception (..)) 
import Control.Applicative                      ((<$>), (<*>))
import Text.PrettyPrint.HughesPJ    
import Data.Aeson    
import SrcLoc                                   (SrcSpan)
import Language.Fixpoint.Misc
import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.RefType
------------------------------------------------------------------------
-- | Pretty Printing Error Messages ------------------------------------
------------------------------------------------------------------------

-- Need to put this here intead of in Types, because it depends on the 
-- printer for SpecTypes, which lives in this module.

instance PPrint Error where
  pprint = ppError

instance Show Error where
  show = showpp

instance Exception Error
instance Exception [Error]

------------------------------------------------------------------------
ppError :: Error -> Doc
------------------------------------------------------------------------

ppError e = ppError' (pprintE $ errSpan e) e
pprintE l = pprint l <> text ": Error:"

ppError' dSp (ErrAssType _ OTerm s r) 
  = dSp <+> text "Termination Check"

ppError' dSp (ErrAssType _ OInv s r) 
  = dSp <+> text "Invariant Check"

ppError' dSp (ErrSubType _ s _ tA tE) 
  = dSp <+> text "Liquid Type Mismatch"
--     DO NOT DELETE EVER! 
     $+$ (nest 4 $ text "Required Type:" <+> pprint tE)
     $+$ (nest 4 $ text "Actual   Type:" <+> pprint tA)

ppError' dSp (ErrParse _ _ e)       
  = dSp <+> text "Cannot parse specification:" 
    $+$ (nest 4 $ pprint e)

ppError' dSp (ErrTySpec _ v t s)       
  = dSp <+> text "Bad Type Specification"
    $+$ (pprint v <+> dcolon <+> pprint t) 
    $+$ (nest 4 $ pprint s)

ppError' dSp (ErrInvt _ t s)
  = dSp <+> text "Bad Invariant Specification" 
    $+$ (nest 4 $ text "invariant " <+> pprint t $+$ pprint s)

ppError' dSp (ErrIAl _ t s)
  = dSp <+> text "Bad Using Specification" 
    $+$ (nest 4 $ text "as" <+> pprint t $+$ pprint s)

ppError' dSp (ErrIAlMis _ t1 t2 s)
  = dSp <+> text "Incompatible Using Specification" 
    $+$ (nest 4 $ (text "using" <+> pprint t1 <+> text "as" <+> pprint t2) $+$ pprint s)

ppError' dSp (ErrMeas _ t s)
  = dSp <+> text "Bad Measure Specification" 
    $+$ (nest 4 $ text "measure " <+> pprint t $+$ pprint s)

ppError' dSp (ErrDupSpecs _ v ls)
  = dSp <+> text "Multiple Specifications for" <+> pprint v <> colon
    $+$ (nest 4 $ vcat $ pprint <$> ls) 

ppError' dSp (ErrDupAlias _ k v ls)
  = dSp <+> text "Multiple Declarations! " 
    $+$ (nest 2 $ text "Multiple Declarations of" <+> pprint k <+> ppVar v $+$ text "Declared at:")
    <+> (nest 4 $ vcat $ pprint <$> ls) 

ppError' dSp (ErrGhc _ s)       
  = dSp <+> text "GHC Error"
    $+$ (nest 4 $ pprint s)

ppError' dSp (ErrMismatch _ x τ t) 
  = dSp <+> text "Specified Type Does Not Refine Haskell Type for" <+> pprint x
    $+$ text "Haskell:" <+> pprint τ
    $+$ text "Liquid :" <+> pprint t 
     
ppError' dSp (ErrSaved _ s)       
  = dSp <+> s

ppError' _ (ErrOther _ s)       
  = text "Panic!" <+> nest 4 (pprint s)


ppVar v = text "`" <> pprint v <> text "'"

instance ToJSON Error where
  toJSON e = object [ "pos" .= (errSpan e)
                    , "msg" .= (render $ ppError' empty e)
                    ]

instance FromJSON Error where
  parseJSON (Object v) = errSaved <$> v .: "pos" 
                                  <*> v .: "msg"
  parseJSON _          = mempty


errSaved :: SrcSpan -> String -> Error
errSaved x = ErrSaved x . text
