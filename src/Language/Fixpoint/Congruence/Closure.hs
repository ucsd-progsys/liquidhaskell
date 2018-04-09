module Language.Fixpoint.Congruence.Closure where 

-- import           Data.Hashable
import           Data.Interned
import           Control.Monad
-- import           Control.Monad.Except      -- (MonadError(..))
import           Control.Monad.State.Strict
import qualified Data.HashMap.Strict        as M
import           Language.Fixpoint.Congruence.Types 
import           Language.Fixpoint.Misc       (ifM)

sat :: CongQuery -> Bool 
sat = undefined

type UF = State UFState

data UFState = U 
  { ufPar   :: M.HashMap Id Term          -- ^ i :-> t      IF term 'i' has union-find parent 't'
  , ufPreds :: M.HashMap Id [(Int, Term)] -- ^ i :-> (j, t) IF term 'i' is 'j'-th arg in application 't'
  }

parent :: Term -> UF (Maybe Term)
parent u = M.lookup (identity u) <$> gets ufPar

find :: Term -> UF Id
find u = do 
  mbU' <- parent u 
  case mbU' of
    Nothing -> return (identity u) 
    Just u' -> find u'  

union :: Term -> Term -> UF () 
union _u _v = undefined -- _TODO 

preds :: Id -> UF [(Int, Term)]
preds = undefined -- _TODO 

isCong :: Term -> Term -> UF Bool 
isCong = undefined -- _TODO 

isEq :: Term -> Term -> UF Bool 
isEq u v = do 
  ui <- find u 
  vi <- find v 
  return (ui == vi)

congMerge :: (Int, Term) -> (Int, Term) -> UF ()
congMerge (i, u) (j, v) 
  | i == j = ifM (isEq u v) 
              (return ())
              (ifM (isCong u v) 
                (merge u v)
                (return ()))
  | otherwise = return ()  

merge :: Term -> Term -> UF ()
merge u v = do 
  ui <- find u
  vi <- find v 
  unless (ui == vi) $ do 
    uPs <- preds ui 
    vPs <- preds vi 
    union u v
    forM_ uPs $ \u' ->
      forM_ vPs $ \v' -> 
        congMerge u' v'

