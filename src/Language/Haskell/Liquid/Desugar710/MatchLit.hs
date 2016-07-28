{-
(c) The University of Glasgow 2006
(c) The GRASP/AQUA Project, Glasgow University, 1992-1998


Pattern-matching literal patterns
-}

{-# LANGUAGE CPP, ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}

module Language.Haskell.Liquid.Desugar710.MatchLit ( dsLit, dsOverLit, hsLitKey, hsOverLitKey
                , tidyLitPat, tidyNPat
                , matchLiterals, matchNPlusKPats, matchNPats
                , warnAboutIdentities, warnAboutEmptyEnumerations
                ) where

-- #include "HsVersions.h"

import {-# SOURCE #-} Language.Haskell.Liquid.Desugar710.Match  ( match )
import {-# SOURCE #-} Language.Haskell.Liquid.Desugar710.DsExpr ( dsExpr )
import Prelude hiding (error)
import DsMonad
import Language.Haskell.Liquid.Desugar710.DsUtils

import HsSyn

import Id
import CoreSyn
import MkCore
import TyCon
import DataCon
import TcHsSyn ( shortCutLit )
import TcType
import Name
import Type
import PrelNames
import TysWiredIn
import Literal
import SrcLoc
import Data.Ratio
import Outputable
import BasicTypes
import DynFlags
import Util
import FastString

{-
************************************************************************
*                                                                      *
                Desugaring literals
        [used to be in DsExpr, but DsMeta needs it,
         and it's nice to avoid a loop]
*                                                                      *
************************************************************************

We give int/float literals type @Integer@ and @Rational@, respectively.
The typechecker will (presumably) have put \tr{from{Integer,Rational}s}
around them.

ToDo: put in range checks for when converting ``@i@''
(or should that be in the typechecker?)

For numeric literals, we try to detect there use at a standard type
(@Int@, @Float@, etc.) are directly put in the right constructor.
[NB: down with the @App@ conversion.]

See also below where we look for @DictApps@ for \tr{plusInt}, etc.
-}

dsLit :: HsLit -> DsM CoreExpr
dsLit (HsStringPrim _ s) = return (Lit (MachStr s))
dsLit (HsCharPrim   _ c) = return (Lit (MachChar c))
dsLit (HsIntPrim    _ i) = return (Lit (MachInt i))
dsLit (HsWordPrim   _ w) = return (Lit (MachWord w))
dsLit (HsInt64Prim  _ i) = return (Lit (MachInt64 i))
dsLit (HsWord64Prim _ w) = return (Lit (MachWord64 w))
dsLit (HsFloatPrim    f) = return (Lit (MachFloat (fl_value f)))
dsLit (HsDoublePrim   d) = return (Lit (MachDouble (fl_value d)))

dsLit (HsChar _ c)       = return (mkCharExpr c)
dsLit (HsString _ str)   = mkStringExprFS str
dsLit (HsInteger _ i _)  = mkIntegerExpr i
dsLit (HsInt _ i)        = do dflags <- getDynFlags
                              return (mkIntExpr dflags i)

dsLit (HsRat r ty) = do
   num   <- mkIntegerExpr (numerator (fl_value r))
   denom <- mkIntegerExpr (denominator (fl_value r))
   return (mkConApp ratio_data_con [Type integer_ty, num, denom])
  where
    (ratio_data_con, integer_ty)
        = case tcSplitTyConApp ty of
                (tycon, [i_ty]) -> -- ASSERT(isIntegerTy i_ty && tycon `hasKey` ratioTyConKey)
                                   (head (tyConDataCons tycon), i_ty)
                x -> pprPanic "dsLit" (ppr x)

dsOverLit :: HsOverLit Id -> DsM CoreExpr
dsOverLit lit = do { dflags <- getDynFlags
                   ; warnAboutOverflowedLiterals dflags lit
                   ; dsOverLit' dflags lit }

dsOverLit' :: DynFlags -> HsOverLit Id -> DsM CoreExpr
-- Post-typechecker, the SyntaxExpr field of an OverLit contains
-- (an expression for) the literal value itself
dsOverLit' dflags (OverLit { ol_val = val, ol_rebindable = rebindable
                           , ol_witness = witness, ol_type = ty })
  | not rebindable
  , Just expr <- shortCutLit dflags val ty = dsExpr expr        -- Note [Literal short cut]
  | otherwise                              = dsExpr witness

{-
Note [Literal short cut]
~~~~~~~~~~~~~~~~~~~~~~~~
The type checker tries to do this short-cutting as early as possible, but
because of unification etc, more information is available to the desugarer.
And where it's possible to generate the correct literal right away, it's
much better to do so.


************************************************************************
*                                                                      *
                 Warnings about overflowed literals
*                                                                      *
************************************************************************

Warn about functions like toInteger, fromIntegral, that convert
between one type and another when the to- and from- types are the
same.  Then it's probably (albeit not definitely) the identity
-}

warnAboutIdentities :: DynFlags -> CoreExpr -> Type -> DsM ()
warnAboutIdentities dflags (Var conv_fn) type_of_conv
  | wopt Opt_WarnIdentities dflags
  , idName conv_fn `elem` conversionNames
  , Just (arg_ty, res_ty) <- splitFunTy_maybe type_of_conv
  , arg_ty `eqType` res_ty  -- So we are converting  ty -> ty
  = warnDs (vcat [ ptext (sLit "Call of") <+> ppr conv_fn <+> dcolon <+> ppr type_of_conv
                 , nest 2 $ ptext (sLit "can probably be omitted")
                 , parens (ptext (sLit "Use -fno-warn-identities to suppress this message"))
           ])
warnAboutIdentities _ _ _ = return ()

conversionNames :: [Name]
conversionNames
  = [ toIntegerName, toRationalName
    , fromIntegralName, realToFracName ]
 -- We can't easily add fromIntegerName, fromRationalName,
 -- because they are generated by literals

warnAboutOverflowedLiterals :: DynFlags -> HsOverLit Id -> DsM ()
warnAboutOverflowedLiterals _dflags _lit
  | otherwise = return ()

{-
Note [Suggest NegativeLiterals]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
If you write
  x :: Int8
  x = -128
it'll parse as (negate 128), and overflow.  In this case, suggest NegativeLiterals.
We get an erroneous suggestion for
  x = 128
but perhaps that does not matter too much.
-}

warnAboutEmptyEnumerations :: DynFlags -> LHsExpr Id -> Maybe (LHsExpr Id) -> LHsExpr Id -> DsM ()
-- Warns about [2,3 .. 1] which returns the empty list
-- Only works for integral types, not floating point
warnAboutEmptyEnumerations _dflags _fromExpr _mThnExpr _toExpr
  | otherwise = return ()


{-
************************************************************************
*                                                                      *
        Tidying lit pats
*                                                                      *
************************************************************************
-}

tidyLitPat :: HsLit -> Pat Id
-- Result has only the following HsLits:
--      HsIntPrim, HsWordPrim, HsCharPrim, HsFloatPrim
--      HsDoublePrim, HsStringPrim, HsString
--  * HsInteger, HsRat, HsInt can't show up in LitPats
--  * We get rid of HsChar right here
tidyLitPat (HsChar src c) = unLoc (mkCharLitPat src c)
tidyLitPat (HsString src s)
  | lengthFS s <= 1     -- Short string literals only
  = unLoc $ foldr (\c pat -> mkPrefixConPat consDataCon
                                             [mkCharLitPat src c, pat] [charTy])
                  (mkNilPat charTy) (unpackFS s)
        -- The stringTy is the type of the whole pattern, not
        -- the type to instantiate (:) or [] with!
tidyLitPat lit = LitPat lit

----------------
tidyNPat :: (HsLit -> Pat Id)   -- How to tidy a LitPat
                 -- We need this argument because tidyNPat is called
                 -- both by Match and by Check, but they tidy LitPats
                 -- slightly differently; and we must desugar
                 -- literals consistently (see Trac #5117)
         -> HsOverLit Id -> Maybe (SyntaxExpr Id) -> SyntaxExpr Id
         -> Pat Id
tidyNPat tidy_lit_pat (OverLit val False _ ty) mb_neg _
        -- False: Take short cuts only if the literal is not using rebindable syntax
        --
        -- Once that is settled, look for cases where the type of the
        -- entire overloaded literal matches the type of the underlying literal,
        -- and in that case take the short cut
        -- NB: Watch out for weird cases like Trac #3382
        --        f :: Int -> Int
        --        f "blah" = 4
        --     which might be ok if we hvae 'instance IsString Int'
        --

  | isIntTy ty,    Just int_lit <- mb_int_lit
                            = mk_con_pat intDataCon    (HsIntPrim    "" int_lit)
  | isWordTy ty,   Just int_lit <- mb_int_lit
                            = mk_con_pat wordDataCon   (HsWordPrim   "" int_lit)
  | isFloatTy ty,  Just rat_lit <- mb_rat_lit = mk_con_pat floatDataCon  (HsFloatPrim  rat_lit)
  | isDoubleTy ty, Just rat_lit <- mb_rat_lit = mk_con_pat doubleDataCon (HsDoublePrim rat_lit)
  | isStringTy ty, Just str_lit <- mb_str_lit
                            = tidy_lit_pat (HsString "" str_lit)
  where
    mk_con_pat :: DataCon -> HsLit -> Pat Id
    mk_con_pat con lit = unLoc (mkPrefixConPat con [noLoc $ LitPat lit] [])

    mb_int_lit :: Maybe Integer
    mb_int_lit = case (mb_neg, val) of
                   (Nothing, HsIntegral _ i) -> Just i
                   (Just _,  HsIntegral _ i) -> Just (-i)
                   _ -> Nothing

    mb_rat_lit :: Maybe FractionalLit
    mb_rat_lit = case (mb_neg, val) of
       (Nothing, HsIntegral _ i) -> Just (integralFractionalLit (fromInteger i))
       (Just _,  HsIntegral _ i) -> Just (integralFractionalLit
                                                             (fromInteger (-i)))
       (Nothing, HsFractional f) -> Just f
       (Just _, HsFractional f)  -> Just (negateFractionalLit f)
       _ -> Nothing

    mb_str_lit :: Maybe FastString
    mb_str_lit = case (mb_neg, val) of
                   (Nothing, HsIsString _ s) -> Just s
                   _ -> Nothing

tidyNPat _ over_lit mb_neg eq
  = NPat (noLoc over_lit) mb_neg eq

{-
************************************************************************
*                                                                      *
                Pattern matching on LitPat
*                                                                      *
************************************************************************
-}

matchLiterals :: [Id]
              -> Type                   -- Type of the whole case expression
              -> [[EquationInfo]]       -- All PgLits
              -> DsM MatchResult

matchLiterals (var:vars) ty sub_groups
  = -- ASSERT( notNull sub_groups && all notNull sub_groups )
    do  {       -- Deal with each group
        ; alts <- mapM match_group sub_groups

                -- Combine results.  For everything except String
                -- we can use a case expression; for String we need
                -- a chain of if-then-else
        ; if isStringTy (idType var) then
            do  { eq_str <- dsLookupGlobalId eqStringName
                ; mrs <- mapM (wrap_str_guard eq_str) alts
                ; return (foldr1 combineMatchResults mrs) }
          else
            return (mkCoPrimCaseMatchResult var ty alts)
        }
  where
    match_group :: [EquationInfo] -> DsM (Literal, MatchResult)
    match_group eqns
        = do dflags <- getDynFlags
             let LitPat hs_lit = firstPat (head eqns)
             match_result <- match vars ty (shiftEqns eqns)
             return (hsLitKey dflags hs_lit, match_result)

    wrap_str_guard :: Id -> (Literal,MatchResult) -> DsM MatchResult
        -- Equality check for string literals
    wrap_str_guard eq_str (MachStr s, mr)
        = do { -- We now have to convert back to FastString. Perhaps there
               -- should be separate MachBytes and MachStr constructors?
               let s'  = mkFastStringByteString s
             ; lit    <- mkStringExprFS s'
             ; let pred = mkApps (Var eq_str) [Var var, lit]
             ; return (mkGuardedMatchResult pred mr) }
    wrap_str_guard _ (l, _) = pprPanic "matchLiterals/wrap_str_guard" (ppr l)

matchLiterals [] _ _ = panic "matchLiterals []"

---------------------------
hsLitKey :: DynFlags -> HsLit -> Literal
-- Get a Core literal to use (only) a grouping key
-- Hence its type doesn't need to match the type of the original literal
--      (and doesn't for strings)
-- It only works for primitive types and strings;
-- others have been removed by tidy
hsLitKey dflags (HsIntPrim    _ i) = mkMachInt  dflags i
hsLitKey dflags (HsWordPrim   _ w) = mkMachWord dflags w
hsLitKey _      (HsInt64Prim  _ i) = mkMachInt64  i
hsLitKey _      (HsWord64Prim _ w) = mkMachWord64 w
hsLitKey _      (HsCharPrim   _ c) = MachChar   c
hsLitKey _      (HsStringPrim _ s) = MachStr    s
hsLitKey _      (HsFloatPrim    f) = MachFloat  (fl_value f)
hsLitKey _      (HsDoublePrim   d) = MachDouble (fl_value d)
hsLitKey _      (HsString _ s)     = MachStr    (fastStringToByteString s)
hsLitKey _      l                  = pprPanic "hsLitKey" (ppr l)

---------------------------
hsOverLitKey :: OutputableBndr a => HsOverLit a -> Bool -> Literal
-- Ditto for HsOverLit; the boolean indicates to negate
hsOverLitKey (OverLit { ol_val = l }) neg = litValKey l neg

---------------------------
litValKey :: OverLitVal -> Bool -> Literal
litValKey (HsIntegral _ i) False = MachInt i
litValKey (HsIntegral _ i) True  = MachInt (-i)
litValKey (HsFractional r) False = MachFloat (fl_value r)
litValKey (HsFractional r) True  = MachFloat (negate (fl_value r))
litValKey (HsIsString _ s) _neg   = {- ASSERT( not neg) -} MachStr
                                                      (fastStringToByteString s)

{-
************************************************************************
*                                                                      *
                Pattern matching on NPat
*                                                                      *
************************************************************************
-}

matchNPats :: [Id] -> Type -> [EquationInfo] -> DsM MatchResult
matchNPats (var:vars) ty (eqn1:eqns)    -- All for the same literal
  = do  { let NPat (L _ lit) mb_neg eq_chk = firstPat eqn1
        ; lit_expr <- dsOverLit lit
        ; neg_lit <- case mb_neg of
                            Nothing -> return lit_expr
                            Just neg -> do { neg_expr <- dsExpr neg
                                           ; return (App neg_expr lit_expr) }
        ; eq_expr <- dsExpr eq_chk
        ; let pred_expr = mkApps eq_expr [Var var, neg_lit]
        ; match_result <- match vars ty (shiftEqns (eqn1:eqns))
        ; return (mkGuardedMatchResult pred_expr match_result) }
matchNPats vars _ eqns = pprPanic "matchOneNPat" (ppr (vars, eqns))

{-
************************************************************************
*                                                                      *
                Pattern matching on n+k patterns
*                                                                      *
************************************************************************

For an n+k pattern, we use the various magic expressions we've been given.
We generate:
\begin{verbatim}
    if ge var lit then
        let n = sub var lit
        in  <expr-for-a-successful-match>
    else
        <try-next-pattern-or-whatever>
\end{verbatim}
-}

matchNPlusKPats :: [Id] -> Type -> [EquationInfo] -> DsM MatchResult
-- All NPlusKPats, for the *same* literal k
matchNPlusKPats (var:vars) ty (eqn1:eqns)
  = do  { let NPlusKPat (L _ n1) (L _ lit) ge minus = firstPat eqn1
        ; ge_expr     <- dsExpr ge
        ; minus_expr  <- dsExpr minus
        ; lit_expr    <- dsOverLit lit
        ; let pred_expr   = mkApps ge_expr [Var var, lit_expr]
              minusk_expr = mkApps minus_expr [Var var, lit_expr]
              (wraps, eqns') = mapAndUnzip (shift n1) (eqn1:eqns)
        ; match_result <- match vars ty eqns'
        ; return  (mkGuardedMatchResult pred_expr               $
                   mkCoLetMatchResult (NonRec n1 minusk_expr)   $
                   adjustMatchResult (foldr1 (.) wraps)         $
                   match_result) }
  where
    shift n1 eqn@(EqnInfo { eqn_pats = NPlusKPat (L _ n) _ _ _ : pats })
        = (wrapBind n n1, eqn { eqn_pats = pats })
        -- The wrapBind is a no-op for the first equation
    shift _ e = pprPanic "matchNPlusKPats/shift" (ppr e)

matchNPlusKPats vars _ eqns = pprPanic "matchNPlusKPats" (ppr (vars, eqns))
