module Language.Haskell.Liquid.LawInstances ( checkLawInstances ) where

import qualified Data.List                                  as L
import qualified Data.Maybe                                 as Mb
import           Text.PrettyPrint.HughesPJ 

import           Language.Haskell.Liquid.Types
import           Language.Haskell.Liquid.Types.Equality
import           Language.Haskell.Liquid.GHC.API            
import qualified Language.Fixpoint.Types                     as F

checkLawInstances :: GhcSpecLaws -> [Error]    
checkLawInstances speclaws = concatMap go (gsLawInst speclaws) 
  where go l = checkOneInstance (lilName l) (Mb.fromMaybe [] $ L.lookup (lilName l) (gsLawDefs speclaws)) l 

checkOneInstance :: Class -> [(Var, LocSpecType)] -> LawInstance -> [Error]
checkOneInstance c laws li 
  = checkExtra c li ((fst <$> laws) ++ classMethods c) (lilEqus li) ++ concatMap (\l -> checkOneLaw c l li) laws

checkExtra :: Class  -> LawInstance -> [Var] -> [(VarOrLocSymbol, (VarOrLocSymbol, Maybe LocSpecType))] -> [Error]
checkExtra c li laws insts = mkError <$> ({- (msgExtra <$> extra) ++ -}  (msgUnfoundLaw <$> unfoundLaws) ++ (msgUnfoundInstance <$> unfoundInstances))
    where 

        unfoundInstances = [ x | (_, (Right x,_)) <- insts] 
        unfoundLaws = [ x | (Right x, _) <- insts] 
        extra = [] -- this breaks on extra super requirements [ (x,i) | (Left x, (Left i, _)) <- insts, not (x `L.elem` laws)] 
        mkError = ErrILaw (lilPos li) (pprint c) (pprint $ lilTyArgs li) 
        msgExtra (x,_)       = pprint x <+> text "is not a defined law."
        msgUnfoundLaw i      = pprint i <+> text "is not a defined law."
        msgUnfoundInstance i = pprint i <+> text "is not a defined instance."

checkOneLaw :: Class -> (Var, LocSpecType) -> LawInstance -> [Error]
checkOneLaw c (x, t) li 
  | Just (Left _, Just ti) <- lix 
  = unify mkError c li t ti
  | Just (Right l, _) <- lix
  = [mkError (text "The instance for the law" <+> pprint x <+> text "is not found")]
  | otherwise
  = [mkError (text "The instance for the law" <+> pprint x <+> text "is not defined")]
  where 
    lix = L.lookup (Left x) (lilEqus li)
    mkError = ErrILaw (lilPos li) (pprint c) (pprint $ lilTyArgs li)

unify :: (Doc -> Error) -> Class -> LawInstance -> LocSpecType -> LocSpecType -> [Error]
unify mkError c li t1 t2 
  = go t12 t22 
  where 
    t22 = fromRTypeRep (trep2 {ty_vars = [], ty_binds = fst <$> args2, ty_args = snd <$> args2, ty_refts = drop (length tc2) (ty_refts trep2)})
    subtsSpec = subts :: ([(TyVar, Type)] -> SpecType -> SpecType)
    t12 = F.subst esubst t11
    t11 = subtsSpec tsubst $ fromRTypeRep (trep1 {ty_vars = [], ty_binds = fst <$> args1, ty_args = snd <$> args1, ty_refts = drop (length tc1) (ty_refts trep1)})
    trep1 = toRTypeRep $ val t1 
    trep2 = toRTypeRep $ val t2 
    (tc1, args1) = splitTypeConstraints $ zip (ty_binds trep1) (ty_args trep1)
    (tc2, args2) = splitTypeConstraints $ zip (ty_binds trep2) (ty_args trep2)
    esubst = F.mkSubst ((zip  (fst <$> args1) ((F.EVar . fst) <$> args2))
                 ++  [(F.symbol x, F.EVar (F.symbol y)) | (Left x, (Left y, _)) <- lilEqus li]
                     )

    tsubst = reverse $ zip ((\(RTV v) -> v) <$> (findTyVars tc1 ++ (ty_var_value <$> concat argVars)))
                 (toType <$> (argBds ++ (((`RVar` mempty) . ty_var_value) <$>ty_vars trep2)))

    (argVars, argBds) = unzip (splitForall [] . val <$> lilTyArgs li)

    splitForall vs (RAllT v t) = splitForall (v:vs) t 
    splitForall vs  t           = (vs, t) 

    findTyVars ((b@(x,RApp cc as _ _):ts)) | rtc_tc cc == classTyCon c 
      = [v | RVar v _ <- as ]
    findTyVars (_:ts) = findTyVars ts 
    findTyVars [] = [] 

    go tt1 tt2 =  if tt1 == tt2 then ok else err
    
    err = [mkError (pprint t1 <+> text "is different than" <+> pprint t2)]
    ok  = []  

splitTypeConstraints :: [(F.Symbol, SpecType)] -> ([(F.Symbol, SpecType)], [(F.Symbol, SpecType)])
splitTypeConstraints = go []  
  where  
    go cs (b@(x,RApp c _ _ _):ts) 
      | isClass c
      = go (b:cs) ts 
    go cs r = (reverse cs, r)
