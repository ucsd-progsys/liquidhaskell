module MiniPosix where
  
import Data.Set
import System.Posix.Types
import System.Posix.Files
import System.Posix.IO hiding (openFd, fdRead, fdWrite, createFile)
import System.FilePath ((</>))


data World = W
{-@ data FIO a <pre :: World -> Prop, post :: World -> a -> World -> Prop> 
  = FIO (rs :: (x:World<pre> -> (a, World)<\y -> {v:World<post x y> | true}>))  @-}
{-@ runState :: forall <pre :: World -> Prop, post :: World -> a -> World -> Prop>. 
                FIO <pre, post> a -> x:World<pre> -> (a, World)<\w -> {v:World<post x w> | true}> @-}
data FIO a  = FIO {runState :: World -> (a, World)}

data Capability = C CapabilityT Privilege
data CapabilityT = File | Directory
data Privilege = Read | Write | Lookup | Create | CreateRestr [Privilege]
               
{-@ measure sel :: World -> Fd -> Set Capability @-}
{-@ measure upd :: World -> Fd -> Set Capability -> World @-}
{-@ measure fd :: FilePath -> Fd @-}
{-@ measure parent :: Fd -> Fd @-}

{-@ predicate HasPriv W T P F = Set_mem (C T P) (sel W F) @-}
{-@ predicate Rd  W F = HasPriv W File Read (fd F) @-}
{-@ predicate Cr  W F = HasPriv W Directory Create (fd F) @-}
{-@ predicate RdFD  W F = HasPriv W File Read F @-}
{-@ predicate CrFD  W F = HasPriv W Directory Create F @-}
{-@ predicate Wr  W F = HasPriv W File Write (fd F) @-}
{-@ predicate Lst W F = HasPriv W File Lookup (fd F) @-}

{- ******************** API **************************** -}
instance Monad FIO where
{-@ instance Monad FIO where
 >>= :: forall < pre   :: World -> Prop 
               , pre2  :: World -> Prop 
               , p     :: a -> Prop
               , post1 :: World -> a -> World -> Prop
               , post2 :: World -> b -> World -> Prop
               , post :: World -> b -> World -> Prop>.
       {w:World<pre> -> x:a -> World<post1 w x> -> World<pre2>}        
       {w:World<pre> -> y:a -> w2:World<post1 w y> -> x:b -> World<post2 w2 x> -> World<post w x>}        
       {w:World -> x:a -> w2:World<post1 w x> -> {v:a | v = x} -> a<p>}
       FIO <pre, post1> a
    -> (a<p> -> FIO <pre2, post2> b)
    -> FIO <pre, post> b ;
 >>  :: forall < pre   :: World -> Prop 
               , pre2  :: World -> Prop 
               , p     :: a -> Prop
               , post1 :: World -> a -> World -> Prop
               , post2 :: World -> b -> World -> Prop
               , post :: World -> b -> World -> Prop>.
       {w:World<pre> -> x:a -> World<post1 w x> -> World<pre2>}        
       {w:World<pre> -> y:a -> w2:World<post1 w y> -> x:b -> World<post2 w2 x> -> World<post w x>}        
       FIO <pre, post1> a
    -> FIO <pre2, post2> b
    -> FIO <pre, post> b ;
 return :: forall <p :: World -> Prop>.
           x:a -> FIO <p, \w0 y -> {w1:World<p> | w0 == w1 && y == x }> a
  @-}  
  (FIO g) >>= f = FIO $ \x -> case g x of {(y, s) -> (runState (f y)) s} 
  (FIO g) >>  f = FIO $ \x -> case g x of {(y, s) -> (runState f    ) s}    
  return w      = FIO $ \x -> (w, x)
  fail          = error
                  
{-@ openFd :: f:FilePath -> _ -> _ -> _ ->
              FIO <{\w -> HasPriv w File Read (fd f)},{\w1 x w2 -> (w1 == w2)}> {v:Fd | v = fd f} @-}
openFd :: FilePath -> OpenMode -> Maybe FileMode -> OpenFileFlags -> FIO Fd
openFd = undefined
         
{-@ fdRead :: f:Fd -> _ -> 
              FIO<{\w -> HasPriv w File Read f},{\w1 x w2 -> (w1 == w2)}> (String, ByteCount) @-}
fdRead :: Fd -> ByteCount -> FIO (String, ByteCount)
fdRead = undefined

{-@ fdWrite :: f:Fd -> _ -> 
              FIO<{\w -> HasPriv w File Write f},{\w1 x w2 -> (w1 == w2)}> ByteCount @-}
fdWrite :: Fd -> String -> FIO ByteCount
fdWrite = undefined
          
{-@ createFile :: f:FilePath -> _ ->
                  FIO<{\w -> CrFD w (parent (fd f))},
                      {\w1 x w2 -> (x = fd f) && (w2 = upd w1 x (sel w1 (parent (fd f))))}> {v:Fd | v = fd f } @-}
createFile :: FilePath -> FileMode -> FIO Fd
createFile = undefined
             
{-@ assume (</>) :: p:{v:FilePath | true } -> c:FilePath -> {v:FilePath | parent (fd v) = (fd p)} @-}
{- ***************************************************** -}

{-@ createTest :: p:FilePath ->
                  FIO<{\w -> RdFD w (parent (fd p)) && CrFD w (parent (fd p)) },
                       \w x -> {v:World | RdFD v x }> Fd @-}
createTest :: FilePath ->  FIO Fd
createTest p = createFile p ownerWriteMode
