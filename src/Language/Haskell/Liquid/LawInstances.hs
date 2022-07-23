{-# LANGUAGE FlexibleContexts #-}
module Language.Haskell.Liquid.LawInstances ( checkLawInstances ) where

import qualified Data.List                                  as L
import qualified Data.Maybe                                 as Mb
import           Text.PrettyPrint.HughesPJ                  hiding ((<>))

import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Types.Equality
import           Liquid.GHC.API            hiding ((<+>), text)
import qualified Language.Fixpoint.Types                    as F

checkLawInstances :: GhcSpecLaws -> Diagnostics
checkLawInstances speclaws = foldMap go (gsLawInst speclaws)
  where go l = checkOneInstance (lilName l) (Mb.fromMaybe [] $ L.lookup (lilName l) (gsLawDefs speclaws)) l

checkOneInstance :: Class -> [(Var, LocSpecType)] -> LawInstance -> Diagnostics
checkOneInstance c laws li
  = checkExtra c li ((fst <$> laws) ++ classMethods c) (lilEqus li) <> foldMap (\l -> checkOneLaw c l li) laws

checkExtra :: Class
           -> LawInstance
           -> [Var]
           -> [(VarOrLocSymbol, (VarOrLocSymbol, Maybe LocSpecType))]
           -> Diagnostics
checkExtra c li _laws insts =
    let allMsgs = {- (msgExtra <$> extra) ++ -} (msgUnfoundLaw <$> unfoundLaws) ++ (msgUnfoundInstance <$> unfoundInstances)
    in mkDiagnostics mempty (mkError <$> allMsgs)
    where
        unfoundInstances = [ x | (_, (Right x,_)) <- insts]
        unfoundLaws = [ x | (Right x, _) <- insts]
        _extra = [] -- this breaks on extra super requirements [ (x,i) | (Left x, (Left i, _)) <- insts, not (x `L.elem` laws)] 
        mkError = ErrILaw (lilPos li) (pprint c) (pprint $ lilTyArgs li)
        _msgExtra (x,_)      = pprint x <+> text "is not a defined law."
        msgUnfoundLaw i      = pprint i <+> text "is not a defined law."
        msgUnfoundInstance i = pprint i <+> text "is not a defined instance."

checkOneLaw :: Class -> (Var, LocSpecType) -> LawInstance -> Diagnostics
checkOneLaw c (x, t) li
  | Just (Left _, Just ti) <- lix
  = unify mkError c li t ti
  | Just (Right _l, _) <- lix
  = mkDiagnostics mempty [mkError (text "is not found.")]
  | otherwise
  = mkDiagnostics mempty [mkError (text "is not defined.")]
  where
    lix = L.lookup (Left x) (lilEqus li)
    mkError txt = ErrILaw (lilPos li) (pprint c) (pprintXs $ lilTyArgs li)
                          (text "The instance for the law" <+> pprint x <+> txt)
    pprintXs [l] = pprint l
    pprintXs xs  = pprint xs

unify :: (Doc -> Error) -> Class -> LawInstance -> LocSpecType -> LocSpecType -> Diagnostics
unify mkError c li t1 t2
  = if t11 =*= t22 then emptyDiagnostics else err
  where
    err = mkDiagnostics mempty [mkError (text "is invalid:\nType" <+> pprint t1 <+> text "\nis different than\n" <+> pprint t2
       --  text "\nesubt1 = " <+> pprint esubst1  
       -- text "\nesubt = " <+> pprint esubst  
       -- text "\ncompared\n" <+> pprint t11 <+> text "\nWITH\n" <+> pprint t22 
           )]

    t22 = fromRTypeRep (trep2 {ty_vars = [], ty_binds = fst <$> args2, ty_args = snd <$> args2, ty_refts = drop (length tc2) (ty_refts trep2)})
    t11 = fromRTypeRep (trep1 { ty_vars = []
                              , ty_binds = fst <$> args2
                              , ty_args = tx . snd <$> args1
                              , ty_refts = F.subst esubst <$> drop (length tc1) (ty_refts trep1)
                              , ty_res = tx $ ty_res trep1})
    tx = subtsSpec tsubst . F.subst esubst
    subtsSpec = subts :: ([(TyVar, Type)] -> SpecType -> SpecType)

    trep1 = toRTypeRep $ val t1 
    trep2 = toRTypeRep $ val t2 
    (tc1, args1) = splitTypeConstraints $ zip (ty_binds trep1) (ty_args trep1)
    (tc2, args2) = splitTypeConstraints $ zip (ty_binds trep2) (ty_args trep2)
    esubst = F.mkSubst (esubst1
                 ++  [(F.symbol x, F.EVar (F.symbol y)) | (Left x, (Left y, _)) <- lilEqus li]
                     )
    esubst1 = zip  (fst <$> args1) (F.EVar . fst <$> args2)

    tsubst = reverse $ zip ((\(RTV v) -> v) <$> (findTyVars tc1 ++ (ty_var_value <$> concat argVars)))
                 (toType False <$> (argBds ++ ((`RVar` mempty) . ty_var_value <$> (fst <$> ty_vars trep2))))

    (argVars, argBds) = unzip (splitForall [] . val <$> lilTyArgs li)

    splitForall vs (RAllT v t _) = splitForall (v:vs) t 
    splitForall vs  t            = (vs, t) 

    findTyVars (((_x, RApp cc as _ _):_ts)) | rtc_tc cc == classTyCon c 
      = [v | RVar v _ <- as ]
    findTyVars (_:ts) = findTyVars ts 
    findTyVars [] = [] 


splitTypeConstraints :: [(F.Symbol, SpecType)] -> ([(F.Symbol, SpecType)], [(F.Symbol, SpecType)])
splitTypeConstraints = go []  
  where  
    go cs (b@(_x, RApp c _ _ _):ts) 
      | isClass c
      = go (b:cs) ts 
    go cs r = (reverse cs, map (\(x, t) -> (x, shiftVV t x)) r)
