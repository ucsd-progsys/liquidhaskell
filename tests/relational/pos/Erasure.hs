--
-- Liquidate your assets: reasoning about resource usage in Liquid Haskell.
--

{-@ LIQUID "--reflection" @-}

{-@ infix <*>  @-}
{-@ infix </>  @-}
{-@ infix <//> @-}
{-@ infix <\>  @-}
{-@ infix <\\> @-}
{-@ infix >>=  @-}
{-@ infix =<<  @-}
{-@ infix >/=  @-}
{-@ infix =/<  @-}
{-@ infix >//= @-}
{-@ infix =//< @-}
{-@ infix >\=  @-}
{-@ infix =\<  @-}
{-@ infix >\\= @-}
{-@ infix =\\< @-}

module Erasure (module Erasure) where

import RTick
import Language.Haskell.Liquid.ProofCombinators

--
-- Erasing all the library's cost annotations. In practice, we define the
-- erase function, ⟨·⟩, as a set of inference rules.
--

--
--       ⟨t⟩ == x
--  -----------------
--   ⟨step m t⟩ == x
--
{-@ assume erase_step :: m:Int -> x:a -> { t:Tick a | erase t == x } -> { erase (step m t) == x } @-}
erase_step :: Int -> a -> Tick a -> Proof
erase_step _ _ _ = ()

--
--
--  -----------------
--   ⟨wait x⟩ == x
--
{-@ assume erase_wait :: x:a -> { erase (wait x) == x } @-}
erase_wait :: a -> Proof
erase_wait _ = ()

--
--
--  ------------------
--   ⟨waitN n x⟩ == x
--
{-@ assume erase_waitN :: n:Int -> x:a -> { erase (waitN n x) == x } @-}
erase_waitN :: Int -> a -> Proof
erase_waitN _ _ = ()

--
--
--  -------------
--   ⟨go x⟩ == x
--
{-@ assume erase_go :: x:a -> { erase (go x) == x } @-}
erase_go :: a -> Proof
erase_go _ = ()

--
--
--  ----------------
--   ⟨goN n x⟩ == x
--
{-@ assume erase_goN :: n:Int -> x:a -> { erase (goN n x) == x } @-}
erase_goN :: Int -> a -> Proof
erase_goN _ _ = ()

--
--        ⟨t⟩ == x
--  ---------------------
--    ⟨fmap f t⟩ == f x
--
{-@ assume erase_fmap :: f:(a -> b) -> x:a -> { t:Tick a | erase t == x } -> { erase (fmap f t) == f x } @-}
erase_fmap :: (a -> b) -> a -> Tick a -> Proof
erase_fmap _ _ _ = ()

--
--        ⟨t⟩ == x
--  ---------------------
--    ⟨wmap f t⟩ == f x
--
{-@ assume erase_wmap :: f:(a -> b) -> x:a -> { t:Tick a | erase t == x } -> { erase (wmap f t) == f x } @-}
erase_wmap :: (a -> b) -> a -> Tick a -> Proof
erase_wmap _ _ _ = ()

--
--        ⟨t⟩ == x
--  -----------------------
--    ⟨wmapN n f t⟩ == f x
--
{-@ assume erase_wmapN
     :: m:Int
     -> f:(a -> b)
     -> x:a
     -> { t:Tick a | erase t == x }
     -> { erase (wmapN m f t) == f x }
@-}
erase_wmapN :: Int -> (a -> b) -> a -> Tick a -> Proof
erase_wmapN _ _ _ _ = ()

--
--        ⟨t⟩ == x
--  ---------------------
--    ⟨gmap f t⟩ == f x
--
{-@ assume erase_gmap
     :: f:(a -> b)
     -> x:a
     -> { t:Tick a | erase t == x }
     -> { erase (gmap f t) == f x }
@-}
erase_gmap :: (a -> b) -> a -> Tick a -> Proof
erase_gmap _ _ _ = ()

--
--        ⟨t⟩ == x
--  ----------------------
--    ⟨gmap n f t⟩ == f x
--
{-@ assume erase_gmapN
     :: m:Int
     -> f:(a -> b)
     -> x:a
     -> { t:Tick a | erase t == x }
     -> { erase (gmapN m f t) == f x }
@-}
erase_gmapN :: Int -> (a -> b) -> a -> Tick a -> Proof
erase_gmapN _ _ _ _ = ()

--
--
--  ----------------
--    ⟨pure x⟩ == x
--
{-@ assume erase_pure :: x:a -> { erase (pure x) == x } @-}
erase_pure :: a -> Proof
erase_pure _ = ()

--
--    ⟨tf⟩ == f   ⟨tx⟩ == x
--  -------------------------
--      ⟨tf <*> tx⟩ == f x
--
{-@ assume erase_app
     :: f:(a -> b)
     -> x:a
     -> { tf:Tick (a -> b) | erase tf == f }
     -> { tx:Tick a | erase tx == x }
     -> { erase (tf <*> tx) == f x }
@-}
erase_app :: (a -> b) -> a -> Tick (a -> b) -> Tick a -> Proof
erase_app _ _ _ _ = ()

--
--    ⟨tf⟩ == f   ⟨tx⟩ == x
--  -------------------------
--      ⟨tf </> tx⟩ == f x
--
{-@ assume erase_wapp
     :: f:(a -> b)
     -> x:a
     -> { tf:Tick (a -> b) | erase tf == f }
     -> { tx:Tick a | erase tx == x }
     -> { erase (tf </> tx) == f x }
@-}
erase_wapp :: (a -> b) -> a -> Tick (a -> b) -> Tick a -> Proof
erase_wapp _ _ _ _ = ()

--
--    ⟨tf⟩ == f   ⟨tx⟩ == x
--  -------------------------
--      ⟨tf <//> tx⟩ == f x
--
{-@ assume erase_wwapp
     :: f:(a -> b)
     -> x:a
     -> { tf:Tick (a -> b) | erase tf == f }
     -> { tx:Tick a | erase tx == x }
     -> { erase (tf <//> tx) == f x }
@-}
erase_wwapp :: (a -> b) -> a -> Tick (a -> b) -> Tick a -> Proof
erase_wwapp _ _ _ _ = ()

--
--    ⟨tf⟩ == f   ⟨tx⟩ == x
--  -------------------------
--      ⟨tf <\> tx⟩ == f x
--
{-@ assume erase_gapp
     :: f:(a -> b)
     -> x:a
     -> { tf:Tick (a -> b) | erase tf == f }
     -> { tx:Tick a | erase tx == x }
     -> { erase (tf <\> tx) == f x }
@-}
erase_gapp :: (a -> b) -> a -> Tick (a -> b) -> Tick a -> Proof
erase_gapp _ _ _ _ = ()

--
--    ⟨tf⟩ == f   ⟨tx⟩ == x
--  -------------------------
--     ⟨tf <\\> tx⟩ == f x
--
{-@ assume erase_ggapp
     :: f:(a -> b)
     -> x:a
     -> { tf:Tick (a -> b) | erase tf == f }
     -> { tx:Tick a | erase tx == x }
     -> { erase (tf <\\> tx) == f x }
@-}
erase_ggapp :: (a -> b) -> a -> Tick (a -> b) -> Tick a -> Proof
erase_ggapp _ _ _ _ = ()

--
--      ⟨tx⟩ == x   ⟨ty⟩ == y
--  -------------------------------
--    ⟨liftA2 f tx ty⟩ == f x y
--
{-@ assume erase_liftA2
     :: f:(a -> b -> c)
     -> x:a
     -> y:b
     -> { tx:Tick a | erase tx == x }
     -> { ty:Tick b | erase ty == y }
     -> { erase (liftA2 f tx ty) == f x y }
@-}
erase_liftA2 :: (a -> b -> c) -> a -> b -> Tick a -> Tick b -> Proof
erase_liftA2 _ _ _ _ _ = ()

--
--
--  ------------------
--    ⟨return x⟩ == x
--
{-@ assume erase_return :: x:a -> { erase (return x) == x } @-}
erase_return :: a -> Proof
erase_return _ = ()

--
--    ⟨t⟩ == x   ⟨g x⟩ == f x
--  ----------------------------
--       ⟨t >>= g⟩ == f x
--
{-@ assume erase_bind
     :: f:(a -> b)
     -> x:a
     -> { t:Tick a | erase t == x }
     -> { g:(a -> Tick b) | erase (g x) == f x }
     -> { erase (t >>= g) == f x }
@-}
erase_bind :: (a -> b) -> a -> Tick a -> (a -> Tick b) -> Proof
erase_bind _ _ _ _ = ()

--
--    ⟨t⟩ == x   ⟨g x⟩ == f x
--  ----------------------------
--       ⟨t =<< g⟩ == f x
--
{-@ assume erase_flipped_bind
     :: f:(a -> b)
     -> x:a
     -> { t:Tick a | erase t == x }
     -> { g:(a -> Tick b) | erase (g x) == f x }
     -> { erase (g =<< t) == f x }
@-}
erase_flipped_bind :: (a -> b) -> a -> Tick a -> (a -> Tick b) -> Proof
erase_flipped_bind _ _ _ _ = ()

--
--    ⟨t⟩ == x   ⟨g x⟩ == f x
--  ----------------------------
--     ⟨eqBind n t g⟩ == f x
--
{-@ assume erase_eqBind
     :: n:Int
     -> f:(a -> b)
     -> x:a
     -> { t:Tick a | erase t == x }
     -> { g:(a -> Tick b) | erase (g x) == f x }
     -> { erase (eqBind n t g) == f x }
@-}
erase_eqBind :: Int -> (a -> b) -> a -> Tick a -> (a -> Tick b) -> Proof
erase_eqBind _ _ _ _ _ = ()

--
--    ⟨t⟩ == x   ⟨g x⟩ == f x
--  ----------------------------
--    ⟨leqBind n t g⟩ == f x
--
{-@ assume erase_leqBind
     :: n:Int
     -> f:(a -> b)
     -> x:a
     -> { t:Tick a | erase t == x }
     -> { g:(a -> Tick b) | erase (g x) == f x }
     -> { erase (leqBind n t g) == f x }
@-}
erase_leqBind :: Int -> (a -> b) -> a -> Tick a -> (a -> Tick b) -> Proof
erase_leqBind _ _ _ _ _ = ()

--
--    ⟨t⟩ == x   ⟨g x⟩ == f x
--  ----------------------------
--    ⟨geqBind n t g⟩ == f x
--
{-@ assume erase_geqBind
     :: n:Int
     -> f:(a -> b)
     -> x:a
     -> { t:Tick a | erase t == x }
     -> { g:(a -> Tick b) | erase (g x) == f x }
     -> { erase (geqBind n t g) == f x }
@-}
erase_geqBind :: Int -> (a -> b) -> a -> Tick a -> (a -> Tick b) -> Proof
erase_geqBind _ _ _ _ _ = ()

--
--   ⟨tf⟩ == f   ⟨tx⟩ == x
--  ------------------------
--     ⟨ap tf tx⟩ == f x
--
{-@ assume erase_ap
     :: f:(a -> b)
     -> x:a
     -> { tf:Tick (a -> b) | erase tf == f }
     -> { tx:Tick a | erase tx == x }
     -> { erase (ap tf tx) == f x }
@-}
erase_ap :: (a -> b) -> a -> Tick (a -> b) -> Tick a -> Proof
erase_ap _ _ _ _ = ()

--
--        ⟨t⟩ == x
--  ---------------------
--    ⟨liftM f t⟩ == f x
--
{-@ assume erase_liftM
     :: f:(a -> b)
     -> x:a
     -> { t:Tick a | erase t == x }
     -> { erase (liftM f t) == f x }
@-}
erase_liftM :: (a -> b) -> a -> Tick a -> Proof
erase_liftM _ _ _ = ()

--
--      ⟨tx⟩ == x   ⟨ty⟩ == y
--  -------------------------------
--    ⟨liftM2 f tx ty⟩ == f x y
--
{-@ assume erase_liftM2
     :: f:(a -> b -> c)
     -> x:a
     -> y:b
     -> { tx:Tick a | erase tx == x }
     -> { ty:Tick b | erase ty == y }
     -> { erase (liftM2 f tx ty) == f x y }
@-}
erase_liftM2 :: (a -> b -> c) -> a -> b -> Tick a -> Tick b -> Proof
erase_liftM2 _ _ _ _ _ = ()

--
--    ⟨t⟩ == x   ⟨g x⟩ == f x
--  ----------------------------
--       ⟨t >/= g⟩ == f x
--
{-@ assume erase_wbind
     :: f:(a -> b)
     -> x:a
     -> { t:Tick a | erase t == x }
     -> { g:(a -> Tick b) | erase (g x) == f x }
     -> { erase (t >/= g) == f x }
@-}
erase_wbind :: (a -> b) -> a -> Tick a -> (a -> Tick b) -> Proof
erase_wbind _ _ _ _ = ()

--
--    ⟨t⟩ == x   ⟨g x⟩ == f x
--  ----------------------------
--       ⟨t =/< g⟩ == f x
--
{-@ assume erase_flipped_wbind
     :: f:(a -> b)
     -> x:a
     -> { t:Tick a | erase t == x }
     -> { g:(a -> Tick b) | erase (g x) == f x }
     -> { erase (g =/< t) == f x }
@-}
erase_flipped_wbind :: (a -> b) -> a -> Tick a -> (a -> Tick b) -> Proof
erase_flipped_wbind _ _ _ _ = ()

--
--    ⟨t⟩ == x   ⟨g x⟩ == f x
--  ----------------------------
--       ⟨t >//= g⟩ == f x
--
{-@ assume erase_wwbind :: f:(a -> b)
     -> x:a
     -> { t:Tick a | erase t == x }
     -> { g:(a -> Tick b) | erase (g x) == f x }
     -> { erase (t >//= g) == f x }
@-}
erase_wwbind :: (a -> b) -> a -> Tick a -> (a -> Tick b) -> Proof
erase_wwbind _ _ _ _ = ()

--
--    ⟨t⟩ == x   ⟨g x⟩ == f x
--  ----------------------------
--       ⟨t =//< g⟩ == f x
--
{-@ assume erase_flipped_wwbind :: f:(a -> b)
     -> x:a
     -> { t:Tick a | erase t == x }
     -> { g:(a -> Tick b) | erase (g x) == f x }
     -> { erase (g =//< t) == f x }
@-}
erase_flipped_wwbind :: (a -> b) -> a -> Tick a -> (a -> Tick b) -> Proof
erase_flipped_wwbind _ _ _ _ = ()

--
--    ⟨t⟩ == x   ⟨g x⟩ == f x
--  ----------------------------
--       ⟨t >\= g⟩ == f x
--
{-@ assume erase_gbind :: f:(a -> b)
     -> x:a
     -> { t:Tick a | erase t == x }
     -> { g:(a -> Tick b) | erase (g x) == f x }
     -> { erase (t >\= g) == f x }
@-}
erase_gbind :: (a -> b) -> a -> Tick a -> (a -> Tick b) -> Proof
erase_gbind _ _ _ _ = ()

--
--    ⟨t⟩ == x   ⟨g x⟩ == f x
--  ----------------------------
--       ⟨t =\< g⟩ == f x
--
{-@ assume erase_flipped_gbind :: f:(a -> b)
     -> x:a
     -> { t:Tick a | erase t == x }
     -> { g:(a -> Tick b) | erase (g x) == f x }
     -> { erase (g =\< t) == f x }
@-}
erase_flipped_gbind :: (a -> b) -> a -> Tick a -> (a -> Tick b) -> Proof
erase_flipped_gbind _ _ _ _ = ()

--
--    ⟨t⟩ == x   ⟨g x⟩ == f x
--  ----------------------------
--       ⟨t >\\= g⟩ == f x
--
{-@ assume erase_ggbind :: f:(a -> b)
     -> x:a
     -> { t:Tick a | erase t == x }
     -> { g:(a -> Tick b) | erase (g x) == f x }
     -> { erase (t >\\= g) == f x }
@-}
erase_ggbind :: (a -> b) -> a -> Tick a -> (a -> Tick b) -> Proof
erase_ggbind _ _ _ _ = ()

--
--    ⟨t⟩ == x   ⟨g x⟩ == f x
--  ----------------------------
--       ⟨t =\\< g⟩ == f x
--
{-@ assume erase_flipped_ggbind :: f:(a -> b)
     -> x:a
     -> { t:Tick a | erase t == x }
     -> { g:(a -> Tick b) | erase (g x) == f x }
     -> { erase (g =\\< t) == f x }
@-}
erase_flipped_ggbind :: (a -> b) -> a -> Tick a -> (a -> Tick b) -> Proof
erase_flipped_ggbind _ _ _ _ = ()

--
--       ⟨t⟩ == x
--  --------------------
--    ⟨⟨pay n t⟩⟩ == x
--
{-@ assume erase_pay :: n:Int
     -> x:a
     -> { t:Tick a | n <= tcost t && erase t == x }
     -> { erase (erase (pay n t)) == x }
@-}
erase_pay :: Int -> a -> Tick a -> Proof
erase_pay _ _ _ = ()

-------------------------------------------------------------------------------
-- | Helper functions:
-------------------------------------------------------------------------------

--
-- Inference rules without any premises are clearly equivalent to 'tval'.
--
{-@ reflect erase @-}
{-@ erase :: Tick a -> a @-}
erase :: Tick a -> a
erase (Tick _ x) = x
