{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE OverloadedStrings   #-}

module Language.Haskell.Liquid.Types.Warnings (
  -- * Warning Type
    TWarning(..)

  -- * Printing Warnings
  , ppWarning
  , ppWarning'
  ) where

import           FastString
import           SrcLoc                      
import           Text.PrettyPrint.HughesPJ 

import           Data.Typeable                (Typeable)
import           GHC.Generics
import           System.FilePath              (normalise)

import           Language.Fixpoint.Types      (pprint, Tidy (..), PPrint (..))
import           Language.Haskell.Liquid.Misc ((<->))

ppWarning :: (PPrint a, Show a) => Tidy -> Doc -> TWarning a -> Doc
ppWarning k dCtx e = 
            ppWarning' k dSp dCtx e
        $+$ hint e
  where
    dSp          = pprint (wrnPos e) <-> text ": Warning:"


data TWarning t =
    WrnUnsafeAssumed  { wrnPos :: !SrcSpan
                      -- , msg :: !Doc
                      -- , ctx :: !(M.HashMap Symbol t)
                      , wrnVar :: !Doc 
                      , wrnThl :: !t 
                      } -- ^ unsound behavior warning

  | WrnUnsafeLazy  { wrnPos :: !SrcSpan
                   -- , msg :: !Doc
                   -- , ctx :: !(M.HashMap Symbol t)
                   , wrnVar :: !Doc 
                   -- , thl :: !t 
                   } -- ^ unsound behavior warning

  | WrnUnsafeVar  { wrnPos :: !SrcSpan
                  -- , msg :: !Doc
                  -- , ctx :: !(M.HashMap Symbol t)
                  , wrnVar :: !Doc 
                  , wrnUnsafeVar :: !Doc 
                  -- , thl :: !t 
                  } -- ^ unsound behavior warning

  deriving (Typeable, Generic , Functor )

ppWarning' :: (PPrint a, Show a) => Tidy -> Doc -> Doc -> TWarning a -> Doc
ppWarning' _td dSp _dCtx err@(WrnUnsafeAssumed _ x t)
  = dSp <+> "The refinement type for `" <-> pprint x <-> "` is assumed, which is unsafe."
        $+$ text "assume" <-> pprint x <-> "::" <+> pprint t 

ppWarning' _td dSp _dCtx err@(WrnUnsafeLazy _ x)
  = dSp <+> "`" <-> pprint x <-> "` is declared as lazy, which is unsafe."

ppWarning' _td dSp _dCtx err@(WrnUnsafeVar _ x unsafeX)
  = dSp <+> "`" <-> pprint unsafeX <-> "` is used in `" <+> pprint x <+> "`, which is unsafe."

hint :: TWarning a -> Doc 
hint e = maybe empty (\d -> "" $+$ ("HINT:" <+> d)) (go e) 
  where
    go (WrnUnsafeLazy {})     = Just unsafeHint
    go (WrnUnsafeAssumed {})  = Just unsafeHint
    go (WrnUnsafeVar {})      = Just unsafeHint
    -- go _                      = Nothing 

    unsafeHint = "Enabled by \"-Wdetect-error\"."


instance PPrint SrcSpan where
  pprintTidy _ = pprSrcSpan

pprSrcSpan :: SrcSpan -> Doc
pprSrcSpan (UnhelpfulSpan s) = text $ unpackFS s
pprSrcSpan (RealSrcSpan s)   = pprRealSrcSpan s

pprRealSrcSpan :: RealSrcSpan -> Doc
pprRealSrcSpan span
  | sline == eline && scol == ecol =
    hcat [ pathDoc <-> colon
         , int sline <-> colon
         , int scol
         ]
  | sline == eline =
    hcat $ [ pathDoc <-> colon
           , int sline <-> colon
           , int scol
           ] ++ if ecol - scol <= 1 then [] else [char '-' <-> int (ecol - 1)]
  | otherwise =
    hcat [ pathDoc <-> colon
         , parens (int sline <-> comma <-> int scol)
         , char '-'
         , parens (int eline <-> comma <-> int ecol')
         ]
 where
   path  = srcSpanFile      span
   sline = srcSpanStartLine span
   eline = srcSpanEndLine   span
   scol  = srcSpanStartCol  span
   ecol  = srcSpanEndCol    span

   pathDoc = text $ normalise $ unpackFS path
   ecol'   = if ecol == 0 then ecol else ecol - 1

instance PPrint (TWarning Doc) where
  pprintTidy k = ppWarning k empty . fmap (pprintTidy Lossy)
