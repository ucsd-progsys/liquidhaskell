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

  -- * Adding a Model of the context
  , WithModel (..), dropModel

  -- * Panic (unexpected failures)
  , UserError
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
-- import           Data.Bifunctor
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
import           Language.Fixpoint.Types      (pprint, showpp, Tidy (..), PPrint (..), Symbol, Expr)
import           Language.Fixpoint.Misc       ({- traceShow, -} dcolon)
import           Language.Haskell.Liquid.Misc (intToString)
import           Text.Parsec.Error            (ParseError)
import qualified Control.Exception as Ex
import           System.Directory
import           System.FilePath
import Data.List    (intersperse )
import           Text.Parsec.Error (errorMessages, showErrorMessages)



instance PPrint ParseError where
  pprintTidy _ e = vcat $ tail $ text <$> ls
    where
      ls         = lines $ showErrorMessages "or" "unknown parse error"
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
errorWithContext :: TError Doc -> IO (CtxError Doc)
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
  | l == l'   = Just (f, l, c, c')
  | otherwise = Nothing
  where
     f        = unpackFS $ srcSpanFile s
     l        = srcSpanStartLine s
     c        = srcSpanStartCol  s
     l'       = srcSpanEndLine   s
     c'       = srcSpanEndCol    s
srcSpanInfo _ = Nothing

getFileLine :: FilePath -> Int -> IO (Maybe String)
getFileLine f i = do
  b <- doesFileExist f
  if b
    then getNth (i - 1) . lines <$> readFile f
    else return Nothing

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
    cursor           = blanks (c - 1) <> pointer (max 1 (c' - c))
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

  | ErrSubTypeModel
               { pos  :: !SrcSpan
               , msg  :: !Doc
               , ctxM  :: !(M.HashMap Symbol (WithModel t))
               , tactM :: !(WithModel t)
               , texp :: !t
               } -- ^ liquid type error with a counter-example

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
               , cond :: t
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

  | ErrDupMeas  { pos :: !SrcSpan
                , var :: !Doc
                , tycon :: !Doc
                , locs:: ![SrcSpan]
                } -- ^ multiple definitions of the same measure


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
                , lqTy  :: !Doc
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
                , dname :: !Doc
                , dpos  :: !SrcSpan
                , msg   :: !Doc 
                }

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

  | ErrSaved    { pos :: !SrcSpan
                , nam :: !Doc
                , msg :: !Doc
                } -- ^ Previously saved error, that carries over after DiffCheck

  | ErrFilePragma { pos :: !SrcSpan
                  }

  | ErrOther    { pos   :: SrcSpan
                , msg   :: !Doc
                } -- ^ Sigh. Other.

  deriving (Typeable, Generic , Functor )

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

instance PPrint UserError where
  pprintTidy k = ppError k empty . fmap (pprintTidy Lossy)

data WithModel t
  = NoModel t
  | WithModel !Doc t
  deriving (Functor, Show, Eq, Generic)

instance NFData t => NFData (WithModel t)

dropModel :: WithModel t -> t
dropModel m = case m of
  NoModel t     -> t
  WithModel _ t -> t

instance PPrint SrcSpan where
  pprintTidy _ = pprSrcSpan

pprSrcSpan :: SrcSpan -> Doc
pprSrcSpan (UnhelpfulSpan s) = text $ unpackFS s
pprSrcSpan (RealSrcSpan s)   = pprRealSrcSpan s

pprRealSrcSpan :: RealSrcSpan -> Doc
pprRealSrcSpan span
  | sline == eline && scol == ecol =
    hcat [ pathDoc <> colon
         , int sline <> colon
         , int scol
         ]
  | sline == eline =
    hcat $ [ pathDoc <> colon
           , int sline <> colon
           , int scol
           ] ++ if ecol - scol <= 1 then [] else [char '-' <> int (ecol - 1)]
  | otherwise =
    hcat [ pathDoc <> colon
         , parens (int sline <> comma <> int scol)
         , char '-'
         , parens (int eline <> comma <> int ecol')
         ]
 where
   path  = srcSpanFile      span
   sline = srcSpanStartLine span
   eline = srcSpanEndLine   span
   scol  = srcSpanStartCol  span
   ecol  = srcSpanEndCol    span

   pathDoc = text $ normalise $ unpackFS path
   ecol'   = if ecol == 0 then ecol else ecol - 1

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

nests :: Foldable t => Int -> t Doc -> Doc
nests n      = foldr (\d acc -> nest n (d $+$ acc)) empty

sepVcat :: Doc -> [Doc] -> Doc
sepVcat d ds = vcat $ intersperse d ds

blankLine :: Doc
blankLine    = sizedText 5 " "

ppFull :: Tidy -> Doc -> Doc
ppFull Full  d = d
ppFull Lossy _ = empty

ppReqInContext :: PPrint t => Tidy -> t -> t -> M.HashMap Symbol t -> Doc
ppReqInContext td tA tE c
  = sepVcat blankLine
      [ nests 2 [ text "Inferred type"
                , text "VV :" <+> pprintTidy td tA]
      , nests 2 [ text "not a subtype of Required type"
                , text "VV :" <+> pprintTidy td tE]
      , nests 2 [ text "In Context"
                , vsep (map (uncurry (pprintBind td)) (M.toList c))
                ]
      ]

pprintBind :: PPrint t => Tidy -> Symbol -> t -> Doc
pprintBind td v t = pprintTidy td v <+> char ':' <+> pprintTidy td t

ppReqModelInContext
  :: (PPrint t) => Tidy -> WithModel t -> t -> (M.HashMap Symbol (WithModel t)) -> Doc
ppReqModelInContext td tA tE c
  = sepVcat blankLine
      [ nests 2 [ text "Inferred type"
                , pprintModel td "VV" tA]
      , nests 2 [ text "not a subtype of Required type"
                , pprintModel td "VV" (NoModel tE)]
      , nests 2 [ text "In Context"
                , vsep (map (uncurry (pprintModel td)) (M.toList c))
                ]
      ]

vsep :: [Doc] -> Doc
vsep = vcat . intersperse (char ' ')

pprintModel :: PPrint t => Tidy -> Symbol -> WithModel t -> Doc
pprintModel td v wm = case wm of
  NoModel t
    -> pprintTidy td v <+> char ':' <+> pprintTidy td t
  WithModel m t
    -> pprintTidy td v <+> char ':' <+> pprintTidy td t $+$
       pprintTidy td v <+> char '=' <+> pprintTidy td m

ppPropInContext :: (PPrint p, PPrint c) => Tidy -> p -> c -> Doc
ppPropInContext td p c
  = sepVcat blankLine
      [ nests 2 [ text "Property"
                , pprintTidy td p]
      , nests 2 [ text "Not provable in context"
                , pprintTidy td c
                ]
      ]

instance ToJSON RealSrcSpan where
  toJSON sp = object [ "filename"  .= f
                     , "startLine" .= l1
                     , "startCol"  .= c1
                     , "endLine"   .= l2
                     , "endCol"    .= c2
                     ]
    where
      (f, l1, c1, l2, c2) = unpackRealSrcSpan sp

unpackRealSrcSpan :: RealSrcSpan -> (String, Int, Int, Int, Int)
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
errSaved sp body = ErrSaved sp (text n) (text $ unlines m)
  where
    n : m        = lines body

--------------------------------------------------------------------------------
ppError' :: (PPrint a, Show a) => Tidy -> Doc -> Doc -> TError a -> Doc
--------------------------------------------------------------------------------
ppError' td dSp dCtx (ErrAssType _ o _ c p)
  = dSp <+> pprintTidy td o
        $+$ dCtx
        $+$ (ppFull td $ ppPropInContext td p c)

ppError' td dSp dCtx (ErrSubType _ _ c tA tE)
  = dSp <+> text "Liquid Type Mismatch"
        $+$ dCtx
        $+$ (ppFull td $ ppReqInContext td tA tE c)

ppError' td dSp dCtx (ErrSubTypeModel _ _ c tA tE)
  = dSp <+> text "Liquid Type Mismatch"
        $+$ dCtx
        $+$ (ppFull td $ ppReqModelInContext td tA tE c)

ppError' td  dSp dCtx (ErrFCrash _ _ c tA tE)
  = dSp <+> text "Fixpoint Crash on Constraint"
        $+$ dCtx
        $+$ (ppFull td $ ppReqInContext td tA tE c)

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

ppError' _ dSp _ (ErrDupMeas _ v t ls)
  = dSp <+> text "Multiple Instance Measures for" <+> pprint v
        <+> text "and" <+> pprint t
        <> colon
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

ppError' _ dSp dCtx (ErrAliasApp _ name dl s)
  = dSp <+> text "Malformed Type Alias Application"
        $+$ dCtx
        $+$ text "Type alias:" <+> pprint name
        $+$ text "Defined at:" <+> pprint dl
        $+$ s 

ppError' _ dSp dCtx (ErrSaved _ name s)
  = dSp <+> name -- <+> "(saved)"
        $+$ dCtx
        $+$ {- nest 4 -} s

ppError' _ dSp dCtx (ErrFilePragma _)
  = dSp <+> text "--idirs, --c-files, and --ghc-option cannot be used in file-level pragmas"
        $+$ dCtx

ppError' _ dSp dCtx (ErrOther _ s)
  = dSp <+> text "Uh oh."
        $+$ dCtx
        $+$ nest 4 s

ppError' _ dSp dCtx (ErrTermin _ xs s)
  = dSp <+> text "Termination Error"
        $+$ dCtx
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

ppVar :: PPrint a => a -> Doc
ppVar v = text "`" <> pprint v <> text "'"
