Case Study: Pointers and ByteStrings
====================================

\begin{comment}

\begin{code}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--diffcheck"     @-}
{-# LANGUAGE ForeignFunctionInterface #-}

module Memory where

import Prelude hiding (null)

import Data.Word
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr
import Foreign.Storable
import System.IO.Unsafe
import Data.ByteString.Internal (c2w, w2c)
import Language.Haskell.Liquid.Prelude

spanByte         :: Word8 -> ByteString -> (ByteString, ByteString)
unsafeHead       :: ByteString -> Word8
create, create'  :: Int -> (Ptr Word8 -> IO ()) -> ByteString
\end{code}
\end{comment}

A large part of the allure of Haskell is its elegant, high-level ADTs
that ensure that programs won't be plagued by problems like the infamous
[SSL heartbleed bug](heartbleed.com).\footnotetext{Assuming, of course, the absence of errors in the compiler and run-time...}
However, another part of Haskell's charm is that when you really really 
need to, you can drop down to low-level pointer twiddling to squeeze the 
most performance out of your machine. But of course, that opens the door 
to the heartbleeds.

Wouldn't it be nice to have have our cake and eat it too? That is wouldn't
it be great if we could twiddle pointers at a low-level and still get the
nice safety assurances of high-level types? In this case study, lets see
how LiquidHaskell lets us do exactly that.


HeartBleeds in Haskell
----------------------

\newthought{Modern Languages} like Haskell are ultimately built upon the
foundation of `C`. Thus, implementation errors could open up unpleasant
vulnerabilities that could easily slither past the type system and even
code inspection.


\newthought{Truncating Strings} As a concrete example, lets look at a
a function that uses the `ByteString` library to truncate strings:

\begin{spec}
chop     :: String -> Int -> String
chop s n = s'
  where 
    b    = B.pack s          -- down to low-level
    b'   = B.unsafeTake n b  -- grab n chars
    s'   = B.unpack b'       -- up to high-level
\end{spec}

\noindent First, the function `pack`s the string into a low-level
bytestring `b`, then it grabs the first `n` `Char`acters from `b`
and translates them back into a high-level `String`. Lets see how
the function works on a small test:

\begin{spec}
ghci> let ex = "Ranjit Loves Burritos"
\end{spec}

\noindent We get the right result when we `chop` a *valid* prefix:

\begin{spec}
ghci> chop ex 10
"Ranjit Lov"
\end{spec}

\noindent But, as illustrated in Figure~\ref{fig:overflow}, the
machine silently reveals (or more colorfully, *bleeds*) the contents
of adjacent memory or if we use an *invalid* prefix:

\begin{spec}
ghci> heartBleed ex 30
"Ranjit Loves Burritos\NUL\201\&1j\DC3\SOH\NUL"
\end{spec}


\begin{figure}[h]
\includegraphics[height=1.0in]{img/overflow.png}
\caption{Can we prevent the program from leaking `secret`s?} 
\label{fig:overflow}
\end{figure}


\newthought{Types against Overflows} Now that we have stared the problem
straight in the eye, look at how we can use LiquidHaskell to *prevent* the
above at compile time. To this end, we decompose the overall system into
a hierarchy of *levels* (i.e. *modules*). In this case, we have three levels:

1. **Machine** level `Pointers`
2. **Library** level `ByteString`
3. **User**    level `Application`

\noindent Now, our strategy, as before, is to develop an *refined API* for
each level such that errors at *each* level are prevented by using the typed
interfaces for the *lower* levels. Next, lets see how this strategy helps develop
a safe means of manipulating pointers.

Low-level Pointer API 
---------------------

To get started, lets look at the low-level pointer API that is
offered by GHC and the run-time. First, lets just see who the
*dramatis personae* are, and how they might let heartbleeds in.
Then, once we have come to grips with the problem, we will see
how to batten down the hatches with LiquidHaskell.

\newthought{Pointers} are an (abstract) type implemented by GHC.
To quote the documentation, "a value of type `Ptr a represents a
pointer to an object, or an array of objects, which may be marshalled
to or from Haskell values of type `a`.

\begin{spec}
data Ptr a         
\end{spec}

\newthought{Foreign Pointers} are *wrapped* pointers that can be
exported to and from C code via the [Foreign Function Interface](foreignptr).

\begin{spec}
data ForeignPtr a 
\end{spec}

\newthought{To Create} a pointer we use `mallocForeignPtrBytes n`
which creates a `Ptr` to a buffer of size `n`, wraps it as a
`ForeignPtr` and returns the result:

\begin{spec}
malloc :: Int -> ForeignPtr a
\end{spec}

\newthought{To Unwrap} and actually use the `ForeignPtr` we use 

\begin{spec}
withForeignPtr :: ForeignPtr a     -- ^ pointer 
               -> (Ptr a -> IO b)  -- ^ action 
               -> IO b             -- ^ result
\end{spec}

\noindent That is, `withForeignPtr fp act` lets us execute a
action `act` on the actual `Ptr` wrapped within the `fp`.
These actions are typically sequences of *dereferences*,
i.e. reads or writes.

\newthought{To Derereference} a pointer, e.g. to read or update
the contents at the corresponding memory location, we use
the functions `peek` and `poke` respectively.
\footnotetext{We elide the `Storable` type class constraint to
strip the presentation down to the absolute essentials.}

\begin{spec}
-- | Read 
peek :: Ptr a -> IO a           

-- | Write
poke :: Ptr a -> a -> IO ()
\end{spec}

\newthought{For Fine Grained Access} we can directly shift
pointers to arbitrary offsets from the blocks obtained via `malloc`.
This is done via the low-level *pointer arithmetic* operation `plusPtr p off`
which takes a pointer `p` an integer `off` and returns the pointer (address)
obtained shifting `p` by `off`:

\begin{spec}
plusPtr :: Ptr a -> Int -> Ptr b 
\end{spec}

\newthought{Example} That was rather dry; lets look at a concrete
example of how one might use the low-level API. The following
function allocates a block of 4 bytes and fills it with zeros:

\begin{code}
zero4 = do fp <- mallocForeignPtrBytes 4
           withForeignPtr fp $ \p -> do
             poke (p `plusPtr` 0) zero 
             poke (p `plusPtr` 1) zero 
             poke (p `plusPtr` 2) zero 
             poke (p `plusPtr` 3) zero 
           return fp
        where
           zero = 0 :: Word8
\end{code}

\noindent While the above is perfectly all right, a small typo could
easily slip past the type system (and run-time!) leading to hard to find
errors:

\begin{code}
zero4' = do fp <- mallocForeignPtrBytes 4
            withForeignPtr fp $ \p -> do
              poke (p `plusPtr` 0) zero 
              poke (p `plusPtr` 1) zero 
              poke (p `plusPtr` 2) zero 
              poke (p `plusPtr` 8) zero 
            return fp
         where
            zero = 0 :: Word8
\end{code}

A Refined Pointer API
---------------------

Wouldn't it be great if we had an assistant to helpfully point out
the error above as soon as we *wrote* it? To turn LiquidHaskell into
this friend, we will use the following strategy: 

1. **Refine pointers** with allocated buffer size
2. **Track sizes** in pointer operations

\newthought{To Refining Pointers} with the *size* of their associated
buffers, we can use an *abstract measure*, i.e. a measure specification  
*without* any underlying implementation.

\footnotetext{These two measures, and the signatures for
the associate API are defined and imported from in the
LiquidHaskell [standard library](https://github.com/ucsd-progsys/liquidhaskell/blob/master/include/GHC/Ptr.spec). We include them here for exposition.}

\begin{spec}
-- | Size of `Ptr`
measure plen  :: Ptr a -> Int 

-- | Size of `ForeignPtr`
measure fplen :: ForeignPtr a -> Int 
\end{spec}

\noindent As before, it is helpful to define a few
aliases for pointers of a given size `N`:

\begin{spec}
type PtrN a N        = {v:Ptr a        | plen v  = N} 
type ForeignPtrN a N = {v:ForeignPtr a | fplen v = N} 
\end{spec}

\newthought{Abstract Measures} are extremely useful when we don't have
a concrete implementation of the underlying value, but we know that
the value *exists*.  \footnotetext{This is another example of a
*ghost* specification} Here, we don't have the value -- inside Haskell
-- because the buffers are manipulated within C. However, this is no
cause for alarm as we will simply use measures to refine the API (not
to perform any computations.)

\newthought{To Refine Allocation} we stipulate that
the size parameter be non-negative, and that the returned
pointer indeed refers to a buffer with exactly `n` bytes:

\begin{spec}
mallocForeignPtrBytes :: n:Nat -> ForeignPtrN a n
\end{spec}

\newthought{To Refine Unwrapping} we specify that the *action*
gets as input, an unwrapped `Ptr` whose size *equals* that of the
given `ForeignPtr`.

\begin{spec}
withForeignPtr :: fp:ForeignPtr a 
               -> (PtrN a (fplen fp) -> IO b)  
               -> IO b             
\end{spec}

\noindent This is a rather interesting *higher-order* specification.
Consider a call `withForeignPtr fp act`. If the `act` requires a `Ptr`
whose size *exceeds* that of `fp` then LiquidHaskell will flag a
(subtyping) error indicating the overflow. If instead the `act`
requires a buffer of size less than `fp` then via contra-variant
function subtyping, the input type of `act` will be widened to
the large size, and the code will be accepted.

\newthought{To Refine Reads and Writes} we specify that they can
only be done if the pointer refers to a non-empty (remaining) buffer.
That is, we define an alias:

\begin{spec}
type OkPtr a = {v:Ptr a | 0 < plen v}
\end{spec}

\noindent that describes pointers referring to *non-empty* buffers
(of strictly positive `plen`), and then use the alias to refine:

\begin{spec}
peek :: OkPtr a -> IO a  
poke :: OkPtr a -> a -> IO ()  
\end{spec}

\noindent In essence the above type says that no matter how arithmetic
was used to shift pointers around, when the actual dereference happens,
the size "remaining" after the pointer must be non-negative (so that a
byte can be safely read from or written to the underlying buffer.)

\newthought{To Refine the Shift} operations, we simply check that the
pointer *remains* within the bounds of the buffer, and update the `plen`
to reflect the size remaining after the shift:
\footnotetext{This signature precludes "left" or "backward" shifts; for
that there is an analogous `minusPtr` which we elide for simplicity}

\begin{spec}
plusPtr :: p:Ptr a -> off:NatLE (plen p) -> PtrN b (plen p - off)      
\end{spec}

\noindent using the alias `NatLE`, defined as:

\begin{spec}
type NatLE N = {v:Nat | v <= N}
\end{spec}

\footnotetext{The alert reader will note that we have strengthened
the type of `plusPtr` to prevent the pointer from wandering outside
the boundary of the buffer. We could instead use a weaker requirement
for `plusPtr` that omits this requirement, and instead have the error
be flagged when the pointer was used to read or write memory.}


\newthought{Types Prevent Overflows} Lets revisit the zero-fill example
from above to understand how the refinements help detect the error:

\begin{code}
exBad = do fp <- mallocForeignPtrBytes 4
           withForeignPtr fp $ \p -> do
             poke (p `plusPtr` 0) zero 
             poke (p `plusPtr` 1) zero 
             poke (p `plusPtr` 2) zero 
             poke (p `plusPtr` 5) zero 
           return fp
        where
           zero = 0 :: Word8
\end{code}


\noindent Lets read the tea leaves to understand the above error:

\begin{liquiderror}
  Error: Liquid Type Mismatch
   Inferred type
     VV : {VV : Int | VV == ?a && VV == 5}
  
   not a subtype of Required type
     VV : {VV : Int | VV <= plen p}
  
   in Context
     zero : {zero : Word8 | zero == ?b}
     VV   : {VV : Int | VV == ?a && VV == (5  :  int)}
     fp   : {fp : ForeignPtr a | fplen fp == ?c && 0 <= fplen fp}
     p    : {p  : Ptr a | fplen fp == plen p && ?c <= plen p && ?b <= plen p && zero <= plen p}
     ?a   : {?a : Int | ?a == 5}
     ?c   : {?c : Int | ?c == 4}
     ?b   : {?b : Integer | ?b == 0}
\end{liquiderror}

\noindent The error says we're bumping `p` up by `VV == 5`
using `plusPtr` but the latter *requires* that bump-offset
be within the size of the buffer referred to by `p`, i.e.
`VV <= plen p`. Indeed, in this context, we have:

\begin{liquiderror}
     p    : {p : Ptr a | fplen fp == plen p && ?c <= plen p && ?b <= plen p && zero <= plen p}
     fp   : {fp : ForeignPtr a | fplen fp == ?c && 0 <= fplen fp}
\end{liquiderror}

\noindent that is, the size of `p`, namely `plen p` equals the size of
`fp`, namely `fplen fp` (thanks to the `withForeignPtr` call), and
finally the latter is equal to `?c` which is `4` bytes. Thus, since
the offset `5` is not less than the buffer size `4`, LiquidHaskell
cannot prove that the call to `plusPtr` is safe, hence the error.


Assumptions vs Guarantees
-------------------------

At this point you ought to wonder: where is the *code* for `peek`,
`poke` or `mallocForeignPtrBytes` and so on? How can we know that the
types we assigned to them are in fact legitimate?

\newthought{Frankly, we cannot} as those functions are *externally*
implemented (in this case, in `C`), and hence, invisible to the
otherwise all-seeing eyes of LiquidHaskell. Thus, we are *assuming* or
*trusting* that those functions behave according to their types. Put
another way, the types for the low-level API are our *specification*
for what low-level pointer safety. We shall now *guarantee* that the
higher level modules that build upon this API in fact use the
low-level function in a manner consistent with this specification.

\newthought{Assumptions are a Feature} and not a bug, as they let
us to verify systems that use some modules for which we do not have
the code. Here, we can *assume* a boundary specification, and then
*guarantee* that the rest of the system is safe with respect to
that specification.
\footnotetext{If we so desire, we can also *check* the boundary
specifications at [run-time](http://en.wikipedia.org/wiki/Design_by_contract),
but that is outside the scope of LiquidHaskell}.


ByteString API
--------------

Next, lets see how the low-level API can be used to implement
to implement [ByteStrings][bytestring], in a way that lets us
perform fast string operations without opening the door to
overflows.


\newthought{A ByteString} is implemented as a record

\begin{code}
data ByteString = BS {
    bPtr :: ForeignPtr Word8
  , bOff :: !Int
  , bLen :: !Int
  }
\end{code}

\noindent comprising

+ a *pointer* `bPtr` to a contiguous block of memory,
+ an *offset* `bOff` that denotes the position inside
  the block where the string begins, and
+ a *length*  `bLen` that denotes the number of bytes
  (from the offset) that belong to the string.

\begin{figure}[h]
\includegraphics[height=1.0in]{img/bytestring.png}
\caption{Representing ByteStrings in memory.}
\label{fig:bytestring}
\end{figure}

These entities are illustrated in Figure~\ref{fig:bytestring}; the
green portion represents the actual contents of a particular
`ByteString`.  This representation makes it possible to implement
various operations like computing prefixes and suffixes extremely
quickly, simply by pointer arithmetic.

\newthought{In a Legal ByteString} the *start* (`bOff`) and *end*
(`bOff + bLen`) offsets lie inside the buffer referred to by the
pointer `bPtr`. We can formalize this invariant with a data definition
that will then make it impossible to create illegal `ByteString`s: 

\begin{code}
{-@ data ByteString = BS {
      bPtr :: ForeignPtr Word8
    , bOff :: {v:Nat| v        <= fplen bPtr}
    , bLen :: {v:Nat| v + bOff <= fplen bPtr}
    }
  @-}
\end{code}

\begin{comment}
-- TODO: we really shouldn't need this...
\begin{code}
{-@ bLen :: b:ByteString -> {v:Nat | v = bLen b} @-}
\end{code}
\end{comment}

\noindent The refinements on `bOff` and `bLen` correspond exactly
to the legality requirements that the start and end of the `ByteString`
be *within* the block of memory referred to by `bPtr`.


\newthought{For brevity} lets define an alias for `ByteString`s of
a given size:

\begin{code}
{-@ type ByteStringN N = {v:ByteString | bLen v = N} @-}
\end{code}

\newthought{Legal Bytestrings}  can be created by directly using
the constructor, as long as we pass in suitable offsets and lengths.
For example,

\begin{code}
{-@ good1 :: IO (ByteStringN 5) @-}
good1 = do fp <- mallocForeignPtrBytes 5
           return (BS fp 0 5)
\end{code}

\noindent creates a valid `ByteString` of size `5`; however we
need not start at the beginning of the block, or use up all
the buffer, and can instead do:

\begin{code}
{-@ good2 :: IO (ByteStringN 2) @-}
good2 = do fp <- mallocForeignPtrBytes 5
           return (BS fp 3 2)
\end{code}

\noindent Note that the length of `good2` is just `2` which is
*less than* allocated size `5`.

\newthought{Illegal Bytestrings} are rejected by LiquidHaskell.
For example, `bad1`'s length is rather more than the buffer
size, and is flagged as such:

\begin{code}
bad1 = do fp <- mallocForeignPtrBytes 3 
          return (BS fp 0 10)
\end{code}

\noindent Similarly, `bad2` does have `2` bytes but *not* if
we start at the offset of `2`:

\begin{code}
bad2 = do fp <- mallocForeignPtrBytes 3
          return (BS fp 2 2)
\end{code}

\exercisen{Fix the ByteString} Modify the definitions of `bad1`
and `bad2` so they are *accepted* by LiquidHaskell.

\newthought{To Flexibly but Safely Create} a `ByteString` the
implementation defines a higher order `create` function, that
takes a size `n` and accepts a `fill` action, and runs the
action after allocating the pointer. After running the action,
the function tucks the pointer into and returns a `ByteString`
of size `n`.

\begin{code}
{-@ create :: n:Nat -> (Ptr Word8 -> IO ()) -> ByteStringN n @-}
create n fill = unsafePerformIO $ do
  fp  <- mallocForeignPtrBytes n
  withForeignPtr fp fill 
  return (BS fp 0 n)
\end{code}

\exercisen{Create} \singlestar Why does LiquidHaskell *reject*
the following function that creates a `ByteString` corresponding
to `"GHC"`?

\begin{code}
bsGHC = create 3 $ \p -> do
  poke (p `plusPtr` 0) (c2w 'G') 
  poke (p `plusPtr` 1) (c2w 'H')
  poke (p `plusPtr` 2) (c2w 'C')
\end{code}

\hint The function writes into 3 slots starting at `p`.
How big should `plen p` be to allow this? What type
does LiquidHaskell infer for `p` above? Does it meet
the requirement? Which part of the *specification*
or *implementation* needs to be modified so that the
relevant information about `p` becomes available within
the `do`-block above? Make sure you figure out the above
before proceeding.

\newthought{To `pack`} a `String` into a `ByteString`
we simply call `create` with the appropriate fill action:
\footnotetext{The code uses `create'` which is just `create`
with the *correct* signature in case you want to skip the previous
exercise. (But don't!)}

\begin{code}
pack str      =  create' n $ \p -> go p xs
  where
  n           = length str
  xs          = map c2w str
  go p (x:xs) = poke p x >> go (plusPtr p 1) xs
  go _ []     = return  ()
\end{code}

\exercisen{Pack} We can compute the size of a `ByteString` by using
the function:

Fix the specification for `pack` so that (it still typechecks!)
and furthermore, the following QuickCheck style *property* is
proved by LiquidHaskell:

\begin{code}
{-@ prop_pack_length  :: [Char] -> {v:Bool | Prop v} @-}
prop_pack_length xs   = bLen (pack xs) == length xs
\end{code}

\hint Look at the type of `length`, and recall that `len`
is a [numeric measure](#numericmeasure) denoting the size
of a list.

\newthought{The magic of inference} ensures that `pack`
just works. Notice there is a tricky little recursive loop
`go` that is used to recursively fill in the `ByteString`
and actually, it has a rather subtle type signature that
LiquidHaskell is able to automatically infer.

\exercise \singlestar Still, we're here to learn, so can you
*write down* the type signature for the loop so that the below
variant of `pack` is accepted by LiquidHaskell (Do this *without*
cheating by peeping at the type inferred for `go` above!)

\begin{code}
packEx str     = create' n $ \p -> pLoop p xs
  where
  n            = length str
  xs           = map c2w str

{-@ pLoop      :: (Storable a) => p:Ptr a -> xs:[a] -> IO () @-}
pLoop p (x:xs) = poke p x >> pLoop (plusPtr p 1) xs
pLoop _ []     = return ()
\end{code}

\hint Remember that `len xs` denotes the size of the list `xs`.

\exercisen{`unsafeTake` and `unsafeDrop`} respectively extract
the prefix and suffix of a `ByteString` from a given position.
They are really fast since we only have to change the offsets.
But why does LiquidHaskell reject them? Can you fix the
specifications so that they are accepted?

\begin{code}
{-@ unsafeTake          :: n:Nat -> b:ByteString -> ByteStringN n @-}
unsafeTake n (BS x s _) = BS x s n

{-@ unsafeDrop          :: n:Nat -> b:ByteString -> ByteStringN {bLen b - n} @-}
unsafeDrop n (BS x s l) = BS x (s + n) (l - n)
\end{code}

\hint Under what conditions are the returned `ByteString`s legal?


\newthought{To `unpack`} a `ByteString` into a plain old `String`,
we essentially run `pack` in reverse, by walking over the pointer,
and reading out the characters one by one till we reach the end:

\begin{code}
unpack              :: ByteString -> String 
unpack (BS _  _ 0)  = []
unpack (BS ps s l)  = unsafePerformIO $ withForeignPtr ps $ \p ->
    go (p `plusPtr` s) (l - 1) []
  where
    {-@ go     :: p:_ -> n:_ -> acc:_ -> IO {v:_ | true } @-}
    go p 0 acc = peek p >>= \e -> return (w2c e : acc)
    go p n acc = peek (p `plusPtr` n) >>=  \e -> go p (n-1) (w2c e : acc)
\end{code}

\exercisen{Unpack} \singlestar Fix the specification for `unpack`
so that the below QuickCheck style property is proved by LiquidHaskell.

\begin{code}
{-@ prop_unpack_length :: ByteString -> {v:Bool | Prop v} @-}
prop_unpack_length b   = bLen b  == length (unpack b)
\end{code}

\hint You will also have to fix the specification of the helper `go`.
Can you determine the output refinement should be (instead of just `true`?)
How *big* is the output list in terms of `p`, `n` and `acc`.


Application API 
---------------

Finally, lets revisit our potentially  "bleeding" `chop` function to see
how the refined `ByteString` API can prevent errors.

\begin{comment}
\begin{code}
{-@ type StringN N = {v:String | len v = N} @-}
{-@ type NatLE N   = {v:Nat    | v <= N}    @-}
\end{code}
\end{comment}

\noindent The signature specifies that the prefix size `n` must be less than
the size of the input string `s`.

\begin{code}
{-@ chop :: s:String -> n:NatLE (len s) -> String @-} 
chop s n = s'
  where 
    b    = pack s          -- down to low-level
    b'   = unsafeTake n b  -- grab n chars
    s'   = unpack b'       -- up to high-level
\end{code}

\newthought{Overflows are prevented} by LiquidHaskell, as it
rejects calls to `chop` where the prefix size is too large
(which is what led to the overflow that spilled the contents
of memory after the string, as illustrated in Figure~\ref{fig:overflow}).
Thus, in the code below, the first use of `chop` which defines `ex6` is accepted
as `6 <= len ex` but the second call is rejected because `30 > len ex`.

\begin{code}
demo     = [ex6, ex30]
  where
    ex   = ['L','I','Q','U','I','D']
    ex6  = chop ex 6   -- accepted by LH 
    ex30 = chop ex 30  -- rejected by LH 
\end{code}

\exercisen{Chop} Fix the specification for `chop` so that
the following property is proved:

\begin{code}
{-@ prop_chop_length  :: String -> Nat -> {v:Bool | Prop v} @-}
prop_chop_length s n
  | n <= length s     = length (chop s n) == n
  | otherwise         = True
\end{code}

Nested ByteStrings 
------------------

For a more in-depth example, let's take a look at `group`,
which transforms strings like

\begin{spec}
`"foobaaar"`
\end{spec}

into *lists* of strings like

\begin{spec}
`["f","oo", "b", "aaa", "r"]`.
\end{spec}

The specification is that `group` should produce a

1. list of *non-empty* `ByteStrings`, 
2. the *sum of* whose lengths equals that of the input string.

\newthought{Non-empty ByteStrings} are those whose length is non-zero:

\begin{code}
{-@ type ByteStringNE = {v:ByteString | bLen v /= 0} @-}
\end{code}

\noindent We can use these to define enrich the ByteString API with a `null` check

\begin{code}
{-@ null               :: b:ByteString -> {v:Bool | Prop v <=> bLen b == 0} @-}
null (BS _ _ l)        = l == 0
\end{code}

\noindent This check is used to determine if it is safe to extract
the head and tail of the `ByteString`. Notice how we can use refinements
to ensure the safety of the operations, and also track the sizes.
\footnotetext{`peekByteOff p i` is equivalent to `peek (plusPtr p i)`}

\begin{code}
{-@ unsafeHead        :: ByteStringNE -> Word8 @-}
unsafeHead (BS x s _) = unsafePerformIO $
                          withForeignPtr x $ \p ->
                            peekByteOff p s

{-@ unsafeTail         :: b:ByteStringNE -> ByteStringN {bLen b - 1} @-}
unsafeTail (BS ps s l) = BS ps (s + 1) (l - 1)
\end{code}

\newthought{The `group`} function recursively calls `spanByte` to carve off
the next group, and then returns the accumulated results:

\begin{code}
{-@ group :: b:ByteString -> {v: [ByteStringNE] | bLens v = bLen b} @-}
group xs
    | null xs   = []
    | otherwise = let  y        = unsafeHead xs
                       (ys, zs) = spanByte y (unsafeTail xs)
                  in (y `cons` ys) : group zs
\end{code}

\noindent The first requirement, that the groups be non-empty is captured by the fact that
the output is a `[ByteStringNE]`. The second requirement, that the sum of the lengths is
preserved, is expressed by a writing a [numeric measure](#numericmeasure):

\begin{code}
{-@ measure bLens @-}
bLens        :: [ByteString] -> Int
bLens []     = 0
bLens (b:bs) = bLen b + bLens bs
\end{code}


\newthought{`spanByte`} does a lot of the heavy lifting. It uses low-level pointer
arithmetic to find the *first* position in the `ByteString` that is different from
the input character `c` and then splits the `ByteString` into a pair comprising the
prefix and suffix at that point.

\begin{code}
{-@ spanByte :: Word8 -> b:ByteString -> ByteString2 b @-}
spanByte c ps@(BS x s l) = unsafePerformIO $ withForeignPtr x $ \p ->
    go  (p `plusPtr` s) 0
  where
    go p i | i >= l    = return (ps, empty)
           | otherwise = do c' <- peekByteOff p i
                            if c /= c'
                                then return (unsafeTake i ps, unsafeDrop i ps)
                                else go  p (i+1)
\end{code}

LiquidHaskell infers that `0 <= i <= l` and therefore that
all of the memory accesses are safe. Furthermore, due to
the precise specifications given to `unsafeTake` and
`unsafeDrop`, it is able to prove that the output pair's
lengths add up to the size of the input `ByteString`.

\begin{code}
{-@ type ByteString2 B = {v:_ | bLen (fst v) + bLen (snd v) = bLen B} @-}
\end{code}

Recap: Types Against Overflows
------------------------------

In this chapter we saw a case study illustrating how measures and refinements
enable safe low-level pointer arithmetic in Haskell. The take away messages are:

1. larger systems are *composed of* layers of smaller ones,
2. we can write *refined APIs* for each layer,
3. that can be used to inform the *design* and
   ensure *correctness* of the layers above.

We saw this in action by developing a low-level `Pointer` API, using it to
implement fast `ByteString`s API, and then building some higher-level
functions on top of the `ByteStrings`.

\newthought{The Trusted Computing Base} in this approach includes
exactly those layers for which the code is *not* available, for
example, because they are implemented outside the language and
accessed via the FFI as with `mallocForeignPtrBytes` and `peek` and
`poke`. In this case, we can make progress by *assuming* the APIs hold
for those layers and verify the rest of the system with respect to
that API.  It is important to note that in the entire case study, it
is only the above FFI signatures that are *trusted*; the rest are all
verified by LiquidHaskell.

\begin{comment}
\begin{code}
-----------------------------------------------------------------------
-- Helper Code
-----------------------------------------------------------------------

{-@ unsafeCreate :: l:Nat -> (PtrN Word8 l -> IO ()) -> ByteStringN l @-}
unsafeCreate n f = create' n f -- unsafePerformIO $ create n f

{-@ qualif PLLen(v:a, p:b) : len v <= plen p @-}
{-@ qualif ForeignPtrN(v:ForeignPtr a, n:int): fplen v = n @-}
{-@ qualif FPLenPLen(v:Ptr a, fp:ForeignPtr a): fplen fp = plen v @-}
{-@ qualif PtrLen(v:Ptr a, xs:List b): plen v = len xs @-}
{-@ qualif PlenEq(v: Ptr a, x: int): x <= plen v @-}

{-@ cons :: Word8 -> b:ByteString -> {v:ByteStringNE | bLen v = bLen b + 1} @-}
cons :: Word8 -> ByteString -> ByteString
cons c (BS x s l) = unsafeCreate (l+1) $ \p -> withForeignPtr x $ \f -> do
        poke p c
        memcpy (p `plusPtr` 1) (f `plusPtr` s) (fromIntegral l)

{-@ empty :: {v:ByteString | bLen v = 0} @-} 
empty :: ByteString
empty = BS nullForeignPtr 0 0

{-@ assume mallocForeignPtrBytes :: n:Nat -> IO (ForeignPtrN a n) @-}
{-@ type ForeignPtrN a N = {v:ForeignPtr a | fplen v = N} @-}
{-@ malloc :: n:Nat -> IO (ForeignPtrN a n) @-}
malloc = mallocForeignPtrBytes 

{-@ assume
    c_memcpy :: dst:PtrV Word8
             -> src:PtrV Word8 
             -> size:{CSize | size <= plen src && size <= plen dst} 
             -> IO (Ptr Word8)
  @-}
foreign import ccall unsafe "string.h memcpy" c_memcpy
    :: Ptr Word8 -> Ptr Word8 -> CSize -> IO (Ptr Word8)

{-@ memcpy :: dst:PtrV Word8
           -> src:PtrV Word8 
           -> size:{CSize | size <= plen src && size <= plen dst} 
           -> IO () 
  @-}
memcpy :: Ptr Word8 -> Ptr Word8 -> CSize -> IO ()
memcpy p q s = c_memcpy p q s >> return ()

{-@ assume nullForeignPtr :: {v: ForeignPtr Word8 | fplen v = 0} @-}
nullForeignPtr :: ForeignPtr Word8
nullForeignPtr = unsafePerformIO $ newForeignPtr_ nullPtr
{-# NOINLINE nullForeignPtr #-}

{-@ create' :: n:Nat -> (PtrN Word8 n -> IO ()) -> ByteStringN n @-}
create' n fill = unsafePerformIO $ do
  fp  <- mallocForeignPtrBytes n
  withForeignPtr fp fill 
  return (BS fp 0 n)

\end{code}

\end{comment}
