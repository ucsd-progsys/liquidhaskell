> {-@ LIQUID "--no-termination" @-}
> {-@ LIQUID "--short-names"    @-}
> {-  LIQUID "--diffcheck"      @-}
> {-# LANGUAGE ForeignFunctionInterface #-}
> 
> module Bytestring where
> 
> import Prelude hiding (null)
> import Data.Char
> import Data.Word
> import Foreign.C.Types
> import Foreign.ForeignPtr
> import Foreign.Ptr
> import Foreign.Storable
> import System.IO.Unsafe
> import Language.Haskell.Liquid.Prelude

Now for some real fun, let's try to prove that `ByteString` is memory-safe! 

`ByteString`s are at the heart of many Haskell applications, e.g. web servers, 
and, as we saw at the beginning of the talk, a bad access can lead to a segfault 
or, even worse, leaking arbitrary memory.

A `ByteString` consists of a pointer into a region of memory, an offset into 
the region, and a length.

> data ByteString = PS { bPayload :: ForeignPtr Word8
>                      , bOffset  :: !Int
>                      , bLength  :: !Int
>                      }

The crucial invariant is that we should only be able to reach valid memory 
locations via the offset and length, i.e. the sum `off + len` *must not exceed* 
the "length" of the pointer.

> {-@ data ByteString = PS
>       { bPayload :: ForeignPtr Word8
>       , bOffset  :: {v:Nat | v           <= fplen bPayload}
>       , bLength  :: {v:Nat | bOffset + v <= fplen bPayload}
>       }
>   @-}

What is the "length" of a pointer? It's the number of bytes that are
addressable from the base of the pointer. We can't compute it, but that
won't stop us from talking about it in our types. We provide a "ghost"
measure called `fplen` to refer to this length.

< {-@ measure fplen :: ForeignPtr a -> Int @-}

and use it to define a foreign-pointer to a segment containing *N* bytes

> {-@ type ForeignN a N = {v:ForeignPtr a | fplen v = N} @-}

Since we haven't defined any equations for `fplen` we won't get strengthed 
constructors. Instead, we will *assume* that `malloc` behaves sensibly and
allocates the number of bytes you asked for.

> {-@ assume mallocForeignPtrBytes :: n:Nat -> IO (ForeignN a n) @-}

Now let's create a few `ByteString`s. Here's a `ByteString` with 5 valid 
indices. 

> good_bs1 = do fp <- mallocForeignPtrBytes 5
>               return $ PS fp 0 5

Note that the *length* of the BS is *not* the same as the region
of allocated memory. 

Here's a `ByteString` whose pointer region has 5-bytes, but the BS itself
is of size 4.
 
> good_bs2 = do fp <- mallocForeignPtrBytes 5
>               return $ PS fp 2 4

LiquidHaskell won't let us build a `ByteString` that claims to have more valid 
indices than it *actually* does

> bad_bs1 = do
>   fp <- mallocForeignPtrBytes 0 
>   return $ PS fp 0 10 

even if we try to be sneaky with the length parameter.

> bad_bs2 = do fp <- mallocForeignPtrBytes 3
>              return $ PS fp 2 2


Creating ByteStrings
--------------------

Nobody actually builds `ByteString`s like this though.

The authors have kindly provided a higher-order function
called `create` to handle the actual allocation. To `create`
a `ByteString` you have to say how many bytes you want and
provide a function that will fill in the newly allocated memory.

> create :: Int -> (Ptr Word8 -> IO ()) -> IO ByteString
> create l f = do
>     fp <- mallocForeignPtrBytes l
>     withForeignPtr fp $ \p -> f p
>     return $! PS fp 0 l

But this seems horribly unsafe!

What's to stop the parameter `f` from poking any random,
invalid offset from the pointer it wants to?

We could, e.g.

* create a BS of size `5`, and
* write a `0` at the index `10`.

ASIDE: have these assumed types around to suppress the type-errors that LH will 
       show, just remove them when script introduces type

> {- assume plusPtr :: p:Ptr a -> n:Int -> Ptr b @-}
> {- assume poke :: Storable a => Ptr a -> a -> IO () @-}

END ASIDE

> bad_create = create 5 $ \p -> poke (p `plusPtr` 10) (0 :: Word8)

which clearly isn't correct. We'd like to say that the provided
function can only address locations a up to a certain offset
from the pointer.

Just as we had `fplen` to talk about the "length" of a `ForeignPtr`,
we have provided `plen` to talk about the "length" of a `Ptr`, and
we've defined a helpful alias

< {-@ type PtrN a N = {v:Ptr a | plen v = N} @-}

which says that a `PtrN a n` has precisely `n` addressable bytes
from its base.


Pointer Arithmetic
------------------

We have also given `plusPtr` the type

< {-@ plusPtr :: p:Ptr a -> n:Int -> {v:Ptr a | plen v = plen p - n} @-}

which says that as you increment a `Ptr`, you're left with fewer addressable
bytes.

Finally, we type `poke` as 

< {-@ poke :: Storable a => {v:Ptr a | 0 <= plen v } -> a -> IO () @-}

which says that the given `Ptr` must be addressable in order to safely `poke` it.

Now we have all of the necessary tools to *prevent* ourselves from
shooting ourselves in the foot with functions like `bad_create`.

We'll just give `create` the type
 
> {-@ create :: l:Nat -> (PtrN Word8 l -> IO ()) -> IO (ByteStringN l) @-}

where the alias

> {-@ type ByteStringN N = {v:ByteString | bLength v = N} @-}

describes `ByteString`s of length `N`.

Lo and behold, LiquidHaskell has flagged `bad_create` as unsafe! 

Furthermore, we can write things like

> good_create = create 5 $ \p -> poke (p `plusPtr` 2) (0 :: Word8)

Here's a real example from the BS library:

> packWith        :: (a -> Word8) -> [a] -> ByteString
> packWith k str  = unsafeCreate (length str) $ \p -> go p str
>   where
>     go _ []     = return ()
>     go p (x:xs) = poke p (k x) >> go (p `plusPtr` 1) xs

proving that `pack` will *never* write out-of-bounds!


Nested Data
-----------

For a more in depth example, let's take a look at `group`,
which transforms strings like

   `"foobaaar"`

into *lists* of strings like

   `["f","oo", "b", "aaa", "r"]`.

The specification is that `group` should produce a list of `ByteStrings`

1. that are all *non-empty* (safety)
2. the sum of whose lengths is equal to the length of the input string (precision)

We use the type alias

> {-@ type ByteStringNE = {v:ByteString | bLength v > 0} @-}

to specify (safety) and introduce a new measure

> {-@ measure bLengths  :: [ByteString] -> Int
>     bLengths ([])   = 0
>     bLengths (x:xs) = (bLength x) + (bLengths xs)
>   @-}

to specify (precision). The full type-specification looks like this:

> {-@ group :: b:ByteString -> {v: [ByteStringNE] | bLengths v = bLength b} @-}
> group xs
>     | null xs   = []
>     | otherwise = let y = unsafeHead xs
>                       (ys, zs) = spanByte (unsafeHead xs) (unsafeTail xs)
>                   in (y `cons` ys) : group zs

As you can probably tell, `spanByte` appears to be doing a lot of the work here,
so let's take a closer look at it to see why the post-condition holds.

> spanByte :: Word8 -> ByteString -> (ByteString, ByteString)
> spanByte c ps@(PS x s l) = unsafePerformIO $ withForeignPtr x $ \p ->
>     go (p `plusPtr` s) 0
>   where
>     go p i | i >= l    = return (ps, empty)
>            | otherwise = do c' <- peekByteOff p i
>                             if c /= c'
>                                 then return (unsafeTake i ps, unsafeDrop i ps)
>                                 else go p (i+1)

LiquidHaskell infers that `0 <= i <= l` and therefore that all of the memory
accesses are safe. Furthermore, due to the precise specifications given to
`unsafeTake` and `unsafeDrop`, it is able to prove that `spanByte` has the type

> {-@ spanByte :: Word8 -> b:ByteString -> (ByteStringPair b) @-}

where `ByteStringPair b` describes a pair of `ByteString`s whose lengths sum to
the length of `b`.

> {-@ type ByteStringPair B = (ByteString, ByteString)<{\x1 x2 ->
>       bLength x1 + bLength x2 = bLength B}> @-}


RJ:LIMITATIONS

Those familiar with the internals of ByteString may notice that we have made a
small change in `group`, the original implementation was

< group :: ByteString -> [ByteString]
< group xs
<     | null xs   = []
<     | otherwise = ys : group zs
<     where
<         (ys, zs) = spanByte (unsafeHead xs) xs

Unfortunately this change was necessary in order to prove the safety invariant,
that `group` returns a list of non-empty `ByteString`s. The real type we would
like to give to `spanByte` (which would enable verification of the original
`group`) would say something like

  `spanByte x b` returns a pair of `ByteString`s, the first of which is non-empty
  *iff* `x = head b`

but it is unclear how to prove this at the moment in LiquidHaskell
(TODO: figure out what would need to change to prove this.)

> -----------------------------------------------------------------------
> -- Helper Code
> -----------------------------------------------------------------------
> {-@ unsafeCreate :: l:Nat -> ((PtrN Word8 l) -> IO ()) -> (ByteStringN l) @-}
> unsafeCreate n f = unsafePerformIO $ create n f
>
> {-@ invariant {v:ByteString   | bLength  v >= 0} @-}
> {-@ invariant {v:[ByteString] | bLengths v >= 0} @-}
> 
> {-@ qualif PLLen(v:a, p:b) : (len v) <= (plen p) @-}
> {-@ qualif ForeignPtrN(v:ForeignPtr a, n:int): fplen v = n @-}
> {-@ qualif FPLenPLen(v:Ptr a, fp:ForeignPtr a): fplen fp = plen v @-}
> {-@ qualif PtrLen(v:Ptr a, xs:List b): plen v = len xs @-}
> {-@ qualif PlenEq(v: Ptr a, x: int): x <= (plen v) @-}
>
> {-@ unsafeHead :: {v:ByteString | (bLength v) > 0} -> Word8 @-}
> unsafeHead :: ByteString -> Word8
> unsafeHead (PS x s l) = liquidAssert (l > 0) $
>   unsafePerformIO  $  withForeignPtr x $ \p -> peekByteOff p s
> 
> {-@ unsafeTail :: b:{v:ByteString | (bLength v) > 0}
>                -> {v:ByteString | (bLength v) = (bLength b) - 1} @-}
> unsafeTail :: ByteString -> ByteString
> unsafeTail (PS ps s l) = liquidAssert (l > 0) $ PS ps (s+1) (l-1)
> 
> {-@ null :: b:ByteString -> {v:Bool | ((Prop v) <=> ((bLength b) = 0))} @-}
> null :: ByteString -> Bool
> null (PS _ _ l) = liquidAssert (l >= 0) $ l <= 0
> 
> {-@ unsafeTake :: n:Nat -> b:{v: ByteString | n <= (bLength v)} -> (ByteStringN n) @-}
> unsafeTake :: Int -> ByteString -> ByteString
> unsafeTake n (PS x s l) = liquidAssert (0 <= n && n <= l) $ PS x s n
> 
> {-@ unsafeDrop :: n:Nat
>                -> b:{v: ByteString | n <= (bLength v)} 
>                -> {v:ByteString | (bLength v) = (bLength b) - n} @-}
> unsafeDrop  :: Int -> ByteString -> ByteString
> unsafeDrop n (PS x s l) = liquidAssert (0 <= n && n <= l) $ PS x (s+n) (l-n)
> 
> {-@ cons :: Word8 -> b:ByteString -> {v:ByteString | (bLength v) = 1 + (bLength b)} @-}
> cons :: Word8 -> ByteString -> ByteString
> cons c (PS x s l) = unsafeCreate (l+1) $ \p -> withForeignPtr x $ \f -> do
>         poke p c
>         memcpy (p `plusPtr` 1) (f `plusPtr` s) (fromIntegral l)
> 
> {-@ empty :: {v:ByteString | (bLength v) = 0} @-} 
> empty :: ByteString
> empty = PS nullForeignPtr 0 0
> 
> {-@ assume
>     c_memcpy :: dst:(PtrV Word8)
>              -> src:(PtrV Word8) 
>              -> size: {v:CSize | (v <= (plen src) && v <= (plen dst))} 
>              -> IO (Ptr Word8)
>   @-}
> foreign import ccall unsafe "string.h memcpy" c_memcpy
>     :: Ptr Word8 -> Ptr Word8 -> CSize -> IO (Ptr Word8)
> 
> {-@ memcpy :: dst:(PtrV Word8)
>            -> src:(PtrV Word8) 
>            -> size: {v:CSize | (v <= (plen src) && v <= (plen dst))} 
>            -> IO () 
>   @-}
> memcpy :: Ptr Word8 -> Ptr Word8 -> CSize -> IO ()
> memcpy p q s = c_memcpy p q s >> return ()
> 
> {-@ assume nullForeignPtr :: {v: ForeignPtr Word8 | (fplen v) = 0} @-}
> nullForeignPtr :: ForeignPtr Word8
> nullForeignPtr = unsafePerformIO $ newForeignPtr_ nullPtr
> {-# NOINLINE nullForeignPtr #-}
