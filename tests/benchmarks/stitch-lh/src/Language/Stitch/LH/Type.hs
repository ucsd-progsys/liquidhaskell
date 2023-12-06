{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Stitch.LH.Type
-- Copyright   :  (C) 2015 Richard Eisenberg
--                (C) 2021 Facundo Domínguez
-- License     :  BSD-style (see LICENSE)
-- Stability   :  experimental
--
-- Defines types
--
----------------------------------------------------------------------------

module Language.Stitch.LH.Type where

import Language.Stitch.LH.Util (Prec, topPrec, maybeParens)

import Prettyprinter
import Data.Hashable
import GHC.Generics

-- | The type of a Stitch expression
data Ty = TInt
        | TBool
        | TFun { funArgTy :: Ty, funResTy :: Ty }
  deriving (Show, Eq, Generic, Hashable)

{-@
data Ty = TInt
        | TBool
        | TFun { funArgTy :: Ty, funResTy :: Ty }
@-}

{-@ measure isFunTy @-}
isFunTy :: Ty -> Bool
isFunTy (TFun _ _) = True
isFunTy _ = False

instance Pretty Ty where
  pretty = pretty_ty topPrec

arrowLeftPrec, arrowRightPrec, arrowPrec :: Prec
arrowLeftPrec  = 5
arrowRightPrec = 4.9
arrowPrec      = 5

pretty_ty :: Prec -> Ty -> Doc ann
pretty_ty p (TFun arg res) = maybeParens (p >= arrowPrec) $
                               hsep [ pretty_ty arrowLeftPrec arg
                                    , pretty "->"
                                    , pretty_ty arrowRightPrec res ]
pretty_ty _    TInt        = pretty "Int"
pretty_ty _    TBool       = pretty "Bool"
