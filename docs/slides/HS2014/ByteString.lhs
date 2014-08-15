> {-@ LIQUID "--no-termination" @-}
> {-@ LIQUID "-g-package-db" @-}
> {-@ LIQUID "-g/Users/gridaphobe/.nix-profile/lib/ghc-7.8.3/package.conf.d/" @-}
> module Main where
> 
> import Data.Char
> import Data.Word
> import Foreign.ForeignPtr
> import Foreign.Ptr
> import Foreign.Storable
> import System.IO.Unsafe

Now for some real fun, let's try to prove that `ByteString` is memory-safe! 
`ByteString`s are at the heart of many Haskell applications, e.g. web servers, 
and, as we saw at the beginning of the talk, a bad access can lead to a segfault 
or, even worse, leaking arbitrary memory.

A `ByteString` consists of a pointer into a region of memory, an offset into 
the region, and a length.

> data ByteString = PS (ForeignPtr Word8) Int Int

The crucial invariant is that we should only be able to reach valid memory 
locations via the offset and length, i.e. the sum `off + len` *must not exceed* 
the "length" of the pointer.

> {-@ data ByteString = PS
>       { bs_pay :: ForeignPtr Word8
>       , bs_off :: {v:Nat | v          <= (fplen bs_pay)}
>       , bs_len :: {v:Nat | bs_off + v <= (fplen bs_pay)} }
>   @-}

What is the "length" of a pointer you ask? It's the number of bytes that are
addressable from the base of the pointer. We can't compute it, but that won't
stop us from talking about it in our types. We provide a "ghost" measure called
`fplen` to refer to this length.

< {-@ measure fplen :: ForeignPtr a -> Int @-}

Since we haven't defined any equations for `fplen` we won't get strengthed 
constructors, and we might have to assume a few things about `fplen`s, for 
instance that `malloc` behaves sensibly and allocates the number of bytes you 
asked for.

> {-@ assume mallocForeignPtrBytes :: n:Nat -> IO (ForeignPtrN a n) @-}

Now let's create a few `ByteString`. Here's a `ByteString` with 5 valid 
indices. 

> good_bs1 = do fp <- mallocForeignPtrBytes 5
>               return $ PS fp 0 5

Here's a similar `ByteString` with only 4 valid indices.

> good_bs2 = do fp <- mallocForeignPtrBytes 5
>               return $ PS fp 1 4

LiquidHaskell won't let us build a `ByteString` that claims to have more valid 
indices than it actually does

> bad_bs1 = do fp <- mallocForeignPtrBytes 0
>              return $ PS fp 0 1

even if we try to be sneaky with the length parameter.

> bad_bs2 = do fp <- mallocForeignPtrBytes 3
>              return $ PS fp 2 2


Creating ByteStrings
--------------------

Nobody actually builds `ByteString`s like this though, the authors have kindly
provided a higher-order function called `create` to handle the actual
allocation. To `create` a `ByteString` you have to say how many bytes you want
and provide a function that will fill in the blanks.

> create :: Int -> (Ptr Word8 -> IO ()) -> IO ByteString
> create l f = do
>     fp <- mallocForeignPtrBytes l
>     withForeignPtr fp $ \p -> f p
>     return $! PS fp 0 l

But this seems horribly unsafe! What's to stop the parameter `f` from poking 
any random, invalid offset from the pointer it wants to? I could, for example, 
write

> bad_create = create 5 $ \p -> poke (p `plusPtr` 10) (0 :: Word8)

which clearly isn't correct. We'd like to say that the provided function can 
only address locations a up to a certain offset from the pointer. Just as we 
had `fplen` to talk about the "length" of a `ForeignPtr`, we have provided 
`plen` to talk about the "length" of a `Ptr`, and we've defined a helpful alias

< {-@ type PtrN a N = {v:Ptr a | plen v = N} @-}

which says that a `PtrN a n` has precisely `n` addressable bytes from its base.
We have also given `plusPtr` the type

< {-@ plusPtr :: p:Ptr a -> n:Int -> {v:Ptr a | plen v = plen p - n} @-}

which says that as you increment a `Ptr`, you're left with fewer addressable bytes.
Finally, we give `poke` the type

< {-@ poke :: Storable a => {v:Ptr a | plen v >= 0} -> a -> IO () @-}

which says that the given `Ptr` must be addressable in order to safely `poke` it.

Now we have all of the necessary tools to prevent ourselves from writing 
functions like `bad_create` and getting away with it. We'll just give `create` 
the type
 
> {-@ create :: l:Nat -> ((PtrN Word8 l) -> IO ()) -> IO (ByteStringN l)   @-}

and, lo and behold, LiquidHaskell has flagged `bad_create` as unsafe! 
Furthermore, we can write things like

> good_create = create 5 $ \p -> poke (p `plusPtr` 2) (0 :: Word8)

or

> packWith :: (a -> Word8) -> [a] -> ByteString
> packWith k str = unsafeCreate (length str) $ \p -> go p str
>     where
>         go _ []     = return ()
>         go p (x:xs) = poke p (k x) >> go (p `plusPtr` 1) xs

> pack = packWith (fromIntegral . ord)

proving that `pack` will *never* write out-of-bounds!


Higher-Order Loops
------------------

TODO: will there be enough time for this? will it be too confusing?



> {-@ type ByteStringN N = {v:ByteString | bs_len v = N} @-}

> {-@ unsafeCreate :: l:Nat -> ((PtrN Word8 l) -> IO ()) -> (ByteStringN l) @-}
> unsafeCreate n f = unsafePerformIO $ create n f

> {-@ qualif PLLen(v:a, p:b) : (len v) <= (plen p) @-}
> {-@ qualif ForeignPtrN(v:ForeignPtr a, n:int): fplen v = n @-}
> {-@ qualif PtrLen(v:Ptr a, xs:List b): plen v = len xs @-}
