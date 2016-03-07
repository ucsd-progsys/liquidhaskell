{-# LANGUAGE ImplicitParams      #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE OverloadedStrings   #-}

-- | This module contains the *types* related creating Errors.
--   It depends only on Fixpoint and basic haskell libraries,
--   and hence, should be importable everywhere.

module Language.Haskell.Liquid.Types.Errors (
  -- * Generic Error Type
    TError (..)

  -- * Error with Source Context
  , CtxError (..)
  , errorWithContext

  -- * Subtyping Obligation Type
  , Oblig (..)

  -- * Panic (unexpected failures)
  , UserError
  --, HiddenType (..)
  , panic
  , panicDoc
  , todo
  , impossible
  , uError

  -- * Printing Errors
  , ppError
  , ppError'

  -- * SrcSpan Helpers
  , realSrcSpan
  , unpackRealSrcSpan
  ) where

import           Prelude                      hiding (error)

import           SrcLoc                      -- (SrcSpan (..), noSrcSpan)
import           FastString
import           GHC.Generics
import           Control.DeepSeq
import           Data.Typeable                (Typeable)
import           Data.Generics                (Data)
import           Data.Maybe
import           Text.PrettyPrint.HughesPJ
import           Data.Aeson hiding (Result)
import qualified Data.HashMap.Strict as M
import           Language.Fixpoint.Types      (showpp, Tidy (..), PPrint (..), pprint, Symbol, Expr, Reft)
import           Language.Fixpoint.Misc (dcolon)
import           Language.Haskell.Liquid.Misc (intToString)
import           Text.Parsec.Error            (ParseError)
import qualified Control.Exception as Ex
import qualified Outputable as Out
import           DynFlags (unsafeGlobalDynFlags)
import Data.List    (intersperse )
import           Text.Parsec.Error (errorMessages, showErrorMessages)



instance PPrint ParseError where
  pprintTidy _ e = vcat $ tail $ map text ls
    where
      ls = lines $ showErrorMessages "or" "unknown parse error"
                                     "expecting" "unexpected" "end of input"
                                     (errorMessages e)

--------------------------------------------------------------------------------
-- | Context information for Error Messages ------------------------------------
--------------------------------------------------------------------------------
data CtxError t = CtxError
  { ctErr :: TError t
  , ctCtx :: Doc
  } deriving (Functor)

instance Eq (CtxError t) where
  e1 == e2 = ctErr e1 == ctErr e2

instance Ord (CtxError t) where
  e1 <= e2 = ctErr e1 <= ctErr e2

--------------------------------------------------------------------------------
errorWithContext :: TError t -> IO (CtxError t)
--------------------------------------------------------------------------------
errorWithContext e = CtxError e <$> srcSpanContext (pos e)

srcSpanContext :: SrcSpan -> IO Doc
srcSpanContext sp
  | Just (f, l, c, c') <- srcSpanInfo sp
  = maybe empty (makeContext l c c') <$> getFileLine f l
  | otherwise
  = return empty

srcSpanInfo :: SrcSpan -> Maybe (FilePath, Int, Int, Int)
srcSpanInfo (RealSrcSpan s)
  | l == l'           = Just (f, l, c, c')
  | otherwise         = Nothing
  where
     f  = unpackFS $ srcSpanFile s
     l  = srcSpanStartLine s
     c  = srcSpanStartCol  s
     l' = srcSpanEndLine   s
     c' = srcSpanEndCol    s
srcSpanInfo _         = Nothing

getFileLine :: FilePath -> Int -> IO (Maybe String)
getFileLine f i = getNth (i - 1) . lines <$> readFile f

getNth :: Int -> [a] -> Maybe a
getNth i xs
  | i < length xs = Just (xs !! i)
  | otherwise     = Nothing

makeContext :: Int -> Int -> Int -> String -> Doc
makeContext l c c' s = vcat [ text ""
                            , lnum l <+> (text s $+$ cursor)
                            , text ""
                            ]
  where
    lnum n           = text (show n) <+> text "|"
    cursor           = blanks (c - 1) <> pointer (c' - c)
    blanks n         = text $ replicate n ' '
    pointer n        = text $ replicate n '^'

--------------------------------------------------------------------------------
-- | Different kinds of Check "Obligations" ------------------------------------
--------------------------------------------------------------------------------

data Oblig
  = OTerm -- ^ Obligation that proves termination
  | OInv  -- ^ Obligation that proves invariants
  | OCons -- ^ Obligation that proves subtyping constraints
  deriving (Generic, Data, Typeable)

instance Show Oblig where
  show OTerm = "termination-condition"
  show OInv  = "invariant-obligation"
  show OCons = "constraint-obligation"

instance NFData Oblig

instance PPrint Oblig where
  pprintTidy _ = ppOblig

ppOblig :: Oblig -> Doc
ppOblig OCons = text "Constraint Check"
ppOblig OTerm = text "Termination Check"
ppOblig OInv  = text "Invariant Check"

--------------------------------------------------------------------------------
-- | Generic Type for Error Messages -------------------------------------------
--------------------------------------------------------------------------------

-- | INVARIANT : all Error constructors should have a pos field

data TError t =
    ErrSubType { pos  :: !SrcSpan
               , msg  :: !Doc
               , ctx  :: !(M.HashMap Symbol t)
               , tact :: !t
               , texp :: !t
               } -- ^ liquid type error

  | ErrFCrash  { pos  :: !SrcSpan
               , msg  :: !Doc
               , ctx  :: !(M.HashMap Symbol t)
               , tact :: !t
               , texp :: !t
               } -- ^ liquid type error

  | ErrAssType { pos  :: !SrcSpan
               , obl  :: !Oblig
               , msg  :: !Doc
               , ctx  :: !(M.HashMap Symbol t)
               , cond :: !Reft
               } -- ^ condition failure error

  | ErrParse    { pos  :: !SrcSpan
                , msg  :: !Doc
                , pErr :: !ParseError
                } -- ^ specification parse error

  | ErrTySpec   { pos :: !SrcSpan
                , var :: !Doc
                , typ :: !t
                , msg :: !Doc
                } -- ^ sort error in specification

  | ErrTermSpec { pos :: !SrcSpan
                , var :: !Doc
                , exp :: !Expr
                , msg :: !Doc
                } -- ^ sort error in specification

  | ErrDupAlias { pos  :: !SrcSpan
                , var  :: !Doc
                , kind :: !Doc
                , locs :: ![SrcSpan]
                } -- ^ multiple alias with same name error

  | ErrDupSpecs { pos :: !SrcSpan
                , var :: !Doc
                , locs:: ![SrcSpan]
                } -- ^ multiple specs for same binder error

  | ErrBadData  { pos :: !SrcSpan
                , var :: !Doc
                , msg :: !Doc
                } -- ^ bad data type specification (?)

  | ErrDataCon  { pos :: !SrcSpan
                , var :: !Doc
                , msg :: !Doc
                } -- ^ refined datacon mismatches haskell datacon

  | ErrInvt     { pos :: !SrcSpan
                , inv :: !t
                , msg :: !Doc
                } -- ^ Invariant sort error

  | ErrIAl      { pos :: !SrcSpan
                , inv :: !t
                , msg :: !Doc
                } -- ^ Using  sort error

  | ErrIAlMis   { pos :: !SrcSpan
                , tAs :: !t
                , tUs :: !t
                , msg :: !Doc
                } -- ^ Incompatible using error

  | ErrMeas     { pos :: !SrcSpan
                , ms  :: !Doc 
                , msg :: !Doc
                } -- ^ Measure sort error

  | ErrHMeas    { pos :: !SrcSpan
                , ms  :: !Doc 
                , msg :: !Doc
                } -- ^ Haskell bad Measure error

  | ErrUnbound  { pos :: !SrcSpan
                , var :: !Doc
                } -- ^ Unbound symbol in specification

  | ErrGhc      { pos :: !SrcSpan
                , msg :: !Doc
                } -- ^ GHC error: parsing or type checking

  | ErrMismatch { pos   :: !SrcSpan -- ^ haskell type location
                , var   :: !Doc
                , hs    :: !Doc
                , lq    :: !Doc
                , lqPos :: !SrcSpan -- ^ lq type location
                } -- ^ Mismatch between Liquid and Haskell types

  | ErrPartPred { pos  :: !SrcSpan
                , ectr :: !Doc
                , var  :: !Doc
                , argN :: !Int
                , expN :: !Int
                , actN :: !Int
                } -- ^ Mismatch in expected/actual args of abstract refinement

  | ErrAliasCycle { pos    :: !SrcSpan
                  , acycle :: ![(SrcSpan, Doc)]
                  } -- ^ Cyclic Refined Type Alias Definitions

  | ErrIllegalAliasApp { pos   :: !SrcSpan
                       , dname :: !Doc
                       , dpos  :: !SrcSpan
                       } -- ^ Illegal RTAlias application (from BSort, eg. in PVar)

  | ErrAliasApp { pos   :: !SrcSpan
                , nargs :: !Int
                , dname :: !Doc
                , dpos  :: !SrcSpan
                , dargs :: !Int
                }

  | ErrSaved    { pos :: !SrcSpan
                , msg :: !Doc
                } -- ^ Previously saved error, that carries over after DiffCheck

  | ErrTermin   { pos  :: !SrcSpan
                , bind :: ![Doc]
                , msg  :: !Doc
                } -- ^ Termination Error

  | ErrRClass   { pos   :: !SrcSpan
                , cls   :: !Doc
                , insts :: ![(SrcSpan, Doc)]
                } -- ^ Refined Class/Interfaces Conflict

  | ErrBadQual  { pos   :: !SrcSpan
                , qname :: !Doc
                , msg   :: !Doc
                } -- ^ Non well sorted Qualifier

  | ErrOther    { pos   :: SrcSpan
                , msg   :: !Doc
                } -- ^ Sigh. Other.

  deriving (Typeable, Generic, Functor)

instance NFData ParseError where
  rnf t = seq t ()

-- FIXME ES: this is very suspicious, why can't we have multiple errors
-- arising from the same span?

instance Eq (TError a) where
  e1 == e2 = errSpan e1 == errSpan e2

instance Ord (TError a) where
  e1 <= e2 = errSpan e1 <= errSpan e2


errSpan :: TError a -> SrcSpan
errSpan =  pos

--------------------------------------------------------------------------------
-- | Simple unstructured type for panic ----------------------------------------
--------------------------------------------------------------------------------
type UserError  = TError Doc

instance PPrint SrcSpan where
  pprintTidy _ = text . showSDoc . Out.ppr
     where
        showSDoc sdoc = Out.renderWithStyle
                        unsafeGlobalDynFlags
                        sdoc (Out.mkUserStyle
                              Out.alwaysQualify
                              Out.AllTheWay)

instance PPrint UserError where
  pprintTidy k = ppError k empty . fmap pprint

instance Show UserError where
  show = showpp

instance Ex.Exception UserError

-- | Construct and show an Error, then crash
uError :: UserError -> a
uError = Ex.throw

-- | Construct and show an Error, then crash
panicDoc :: {- (?callStack :: CallStack) => -} SrcSpan -> Doc -> a
panicDoc sp d = Ex.throw (ErrOther sp d :: UserError)

-- | Construct and show an Error, then crash
panic :: {- (?callStack :: CallStack) => -} Maybe SrcSpan -> String -> a
panic sp d = panicDoc (sspan sp) (text d)
  where
    sspan  = fromMaybe noSrcSpan

-- | Construct and show an Error with an optional SrcSpan, then crash
--   This function should be used to mark unimplemented functionality
todo :: {- (?callStack :: CallStack) => -} Maybe SrcSpan -> String -> a
todo s m  = panic s $ unlines
            [ "This functionality is currently unimplemented. "
            , "If this functionality is critical to you, please contact us at: "
            , "https://github.com/ucsd-progsys/liquidhaskell/issues"
            , m
            ]

-- | Construct and show an Error with an optional SrcSpan, then crash
--   This function should be used to mark impossible-to-reach codepaths
impossible :: {- (?callStack :: CallStack) => -} Maybe SrcSpan -> String -> a
impossible s m = panic s $ unlines msg ++ m
   where
      msg = [ "This should never happen! If you are seeing this message, "
            , "please submit a bug report at "
            , "https://github.com/ucsd-progsys/liquidhaskell/issues "
            , "with this message and the source file that caused this error."
            , ""
            ]



-- type CtxError = Error
--------------------------------------------------------------------------------
ppError :: (PPrint a, Show a) => Tidy -> Doc -> TError a -> Doc
--------------------------------------------------------------------------------
ppError k dCtx e = ppError' k dSp dCtx e
  where
    dSp          = pprint (pos e) <> text ": Error:"

nests n      = foldr (\d acc -> nest n (d $+$ acc)) empty
sepVcat d ds = vcat $ intersperse d ds
blankLine    = sizedText 5 " "

ppFull :: Tidy -> Doc -> Doc
ppFull Full  d = d
ppFull Lossy _ = empty

ppReqInContext :: (PPrint t, PPrint c) => t -> t -> c -> Doc
ppReqInContext tA tE c
  = sepVcat blankLine
      [ nests 2 [ text "Inferred type"
                , text "VV :" <+> pprint tA]
      , nests 2 [ text "not a subtype of Required type"
                , text "VV :" <+> pprint tE]
      , nests 2 [ text "In Context"
                , pprint c                 ]]


ppPropInContext :: (PPrint p, PPrint c) => p -> c -> Doc
ppPropInContext p c
  = sepVcat blankLine
      [ nests 2 [ text "Property"
                , pprint p]
      , nests 2 [ text "Not provable in context"
                , pprint c                 ]]

{-
pprintCtx :: (PTable c) => c -> Doc
pprintCtx = pprint . ptable

instance (PPrint a, PPrint b) => PTable (M.HashMap a b) where
  ptable t = DocTable [ (pprint k, pprint v) | (k, v) <- M.toList t]


pprintKVs :: (PPrint k, PPrint v) => [(k, v)] -> Doc
pprintKVs = vcat . punctuate (text "\n") . map pp1
  where
    pp1 (x,y) = pprint x <+> text ":=" <+> pprint y
-}



instance ToJSON RealSrcSpan where
  toJSON sp = object [ "filename"  .= f  -- (unpackFS $ srcSpanFile sp)
                     , "startLine" .= l1 -- srcSpanStartLine sp
                     , "startCol"  .= c1 -- srcSpanStartCol  sp
                     , "endLine"   .= l2 -- srcSpanEndLine   sp
                     , "endCol"    .= c2 -- srcSpanEndCol    sp
                     ]
    where
      (f, l1, c1, l2, c2) = unpackRealSrcSpan sp

unpackRealSrcSpan rsp = (f, l1, c1, l2, c2)
  where
    f                 = unpackFS $ srcSpanFile rsp
    l1                = srcSpanStartLine rsp
    c1                = srcSpanStartCol  rsp
    l2                = srcSpanEndLine   rsp
    c2                = srcSpanEndCol    rsp


instance FromJSON RealSrcSpan where
  parseJSON (Object v) = realSrcSpan <$> v .: "filename"
                                     <*> v .: "startLine"
                                     <*> v .: "startCol"
                                     <*> v .: "endLine"
                                     <*> v .: "endCol"
  parseJSON _          = mempty

realSrcSpan :: FilePath -> Int -> Int -> Int -> Int -> RealSrcSpan
realSrcSpan f l1 c1 l2 c2 = mkRealSrcSpan loc1 loc2
  where
    loc1                  = mkRealSrcLoc (fsLit f) l1 c1
    loc2                  = mkRealSrcLoc (fsLit f) l2 c2

instance ToJSON SrcSpan where
  toJSON (RealSrcSpan rsp) = object [ "realSpan" .= True, "spanInfo" .= rsp ]
  toJSON (UnhelpfulSpan _) = object [ "realSpan" .= False ]

instance FromJSON SrcSpan where
  parseJSON (Object v) = do tag <- v .: "realSpan"
                            case tag of
                              False -> return noSrcSpan
                              True  -> RealSrcSpan <$> v .: "spanInfo"
  parseJSON _          = mempty

instance (PPrint a, Show a) => ToJSON (TError a) where
  toJSON e = object [ "pos" .= (pos e)
                    , "msg" .= (render $ ppError' Full empty empty e)
                    ]

instance FromJSON (TError a) where
  parseJSON (Object v) = errSaved <$> v .: "pos"
                                  <*> v .: "msg"
  parseJSON _          = mempty

errSaved :: SrcSpan -> String -> TError a
errSaved x = ErrSaved x . text

--------------------------------------------------------------------------------
ppError' :: (PPrint a, Show a) => Tidy -> Doc -> Doc -> TError a -> Doc
--------------------------------------------------------------------------------
ppError' td dSp dCtx (ErrAssType _ o _ c p)
  = dSp <+> pprint o
        $+$ dCtx
        $+$ (ppFull td $ ppPropInContext p c)

ppError' td dSp dCtx (ErrSubType _ _ c tA tE)
  = dSp <+> text "Liquid Type Mismatch"
        $+$ dCtx
        $+$ (ppFull td $ ppReqInContext tA tE c)

ppError' td  dSp dCtx (ErrFCrash _ _ c tA tE)
  = dSp <+> text "Fixpoint Crash on Constraint"
        $+$ dCtx
        $+$ (ppFull td $ ppReqInContext tA tE c)

ppError' _ dSp dCtx (ErrParse _ _ e)
  = dSp <+> text "Cannot parse specification:"
        $+$ dCtx
        $+$ (nest 4 $ pprint e)

ppError' _ dSp _ (ErrTySpec _ v t s)
  = dSp <+> text "Bad Type Specification"
        $+$ (pprint v <+> dcolon <+> pprint t)
        $+$ (nest 4 $ pprint s)

ppError' _ dSp _ (ErrBadData _ v s)
  = dSp <+> text "Bad Data Specification"
        $+$ (pprint v <+> dcolon <+> pprint s)

ppError' _ dSp dCtx (ErrDataCon _ d s)
  = dSp <+> "Malformed refined data constructor" <+> pprint d
        $+$ dCtx
        $+$ s

ppError' _ dSp dCtx (ErrBadQual _ n d)
  = dSp <+> text "Bad Qualifier Specification for" <+> n
        $+$ dCtx
        $+$ (pprint d)

ppError' _ dSp _ (ErrTermSpec _ v e s)
  = dSp <+> text "Bad Termination Specification"
        $+$ (pprint v <+> dcolon <+> pprint e)
        $+$ (nest 4 $ pprint s)

ppError' _ dSp _ (ErrInvt _ t s)
  = dSp <+> text "Bad Invariant Specification"
        $+$ (nest 4 $ text "invariant " <+> pprint t $+$ pprint s)

ppError' _ dSp _ (ErrIAl _ t s)
  = dSp <+> text "Bad Using Specification"
        $+$ (nest 4 $ text "as" <+> pprint t $+$ pprint s)

ppError' _ dSp _ (ErrIAlMis _ t1 t2 s)
  = dSp <+> text "Incompatible Using Specification"
        $+$ (nest 4 $ (text "using" <+> pprint t1 <+> text "as" <+> pprint t2) $+$ pprint s)

ppError' _ dSp _ (ErrMeas _ t s)
  = dSp <+> text "Bad Measure Specification"
        $+$ (nest 4 $ text "measure " <+> pprint t $+$ pprint s)

ppError' _ dSp _ (ErrHMeas _ t s)
  = dSp <+> text "Cannot promote Haskell function" <+> pprint t <+> text "to logic"
        $+$ (nest 4 $ pprint s)

ppError' _ dSp _ (ErrDupSpecs _ v ls)
  = dSp <+> text "Multiple Specifications for" <+> pprint v <> colon
        $+$ (nest 4 $ vcat $ pprint <$> ls)

ppError' _ dSp _ (ErrDupAlias _ k v ls)
  = dSp <+> text "Multiple Declarations! "
    $+$ (nest 2 $ text "Multiple Declarations of" <+> pprint k <+> ppVar v $+$ text "Declared at:")
    <+> (nest 4 $ vcat $ pprint <$> ls)

ppError' _ dSp dCtx (ErrUnbound _ x)
  = dSp <+> text "Unbound variable" <+> pprint x
        $+$ dCtx

ppError' _ dSp dCtx (ErrGhc _ s)
  = dSp <+> text "GHC Error"
        $+$ dCtx
        $+$ (nest 4 $ pprint s)

ppError' _ dSp dCtx (ErrPartPred _ c p i eN aN)
  = dSp <+> text "Malformed Predicate Application"
        $+$ dCtx
        $+$ (nest 4 $ vcat [ "The" <+> text (intToString i) <+> "argument of" <+> c <+> "is predicate" <+> p
                           , "which expects" <+> pprint eN <+> "arguments" <+> "but is given only" <+> pprint aN
                           , "Abstract predicates cannot be partially applied, see "
                           , nest 2 "https://github.com/ucsd-progsys/liquidhaskell/issues/594"
                           , "for possible fix."
                           ])

ppError' _ dSp dCtx (ErrMismatch _ x τ t hsSp)
  = dSp <+> "Specified Type Does Not Refine Haskell Type for" <+> pprint x
        $+$ dCtx
        $+$ (sepVcat blankLine
              [ "The Liquid type"
              , nest 4 t
              , "is inconsistent with the Haskell type"
              , nest 4 τ
              , "defined at" <+> pprint hsSp
              ])

ppError' _ dSp _ (ErrAliasCycle _ acycle)
  = dSp <+> text "Cyclic Alias Definitions"
        $+$ text "The following alias definitions form a cycle:"
        $+$ (nest 4 $ sepVcat blankLine $ map describe acycle)
  where
    describe (p, n)
      =   text "Type alias:" <+> pprint n
      $+$ text "Defined at:" <+> pprint p

ppError' _ dSp dCtx (ErrIllegalAliasApp _ dn dl)
  = dSp <+> text "Refinement Type Alias cannot be used in this context"
        $+$ dCtx
        $+$ text "Type alias:" <+> pprint dn
        $+$ text "Defined at:" <+> pprint dl

ppError' _ dSp dCtx (ErrAliasApp _ n name dl dn)
  = dSp <+> text "Malformed Type Alias Application"
        $+$ dCtx
        $+$ text "Type alias:" <+> pprint name
        $+$ text "Defined at:" <+> pprint dl
        $+$ text "Expects"     <+> pprint dn <+> text "arguments, but is given" <+> pprint n

ppError' _ dSp _ (ErrSaved _ s)
  = dSp <+> s

ppError' _ dSp dCtx (ErrOther _ s)
  = dSp <+> text "Uh oh."
        $+$ dCtx
        $+$ nest 4 s

ppError' _ dSp _ (ErrTermin _ xs s)
  = dSp <+> text "Termination Error"
        <+> (hsep $ intersperse comma xs) $+$ s

ppError' _ dSp _ (ErrRClass p0 c is)
  = dSp <+> text "Refined classes cannot have refined instances"
    $+$ (nest 4 $ sepVcat blankLine $ describeCls : map describeInst is)
  where
    describeCls
      =   text "Refined class definition for:" <+> c
      $+$ text "Defined at:" <+> pprint p0
    describeInst (p, t)
      =   text "Refined instance for:" <+> t
      $+$ text "Defined at:" <+> pprint p

ppVar v = text "`" <> pprint v <> text "'"
