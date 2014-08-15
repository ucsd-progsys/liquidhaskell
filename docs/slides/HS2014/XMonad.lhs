> {-@ LIQUID "--no-termination" @-}
> {-@ LIQUID "-g-package-db" @-}
> {-@ LIQUID "-g/Users/gridaphobe/.nix-profile/lib/ghc-7.8.3/package.conf.d/" @-}
> module Main where

> import qualified Data.Map as M

> data Stack a = Stack
>   { focus :: a   
>   , up    :: [a] 
>   , down  :: [a]
>   }
>
> data Workspace i l a = Workspace 
>   { tag    :: i
>   , layout :: l
>   , stack  :: Maybe (Stack a)
>   }
>
> data Screen i l a sid sd = Screen 
>   { workspace    :: Workspace i l a
>   , screen       :: sid
>   , screenDetail :: sd
>   }
>
> data StackSet i l a sid sd = StackSet 
>   { current  :: Screen i l a sid sd  
>   , visible  :: [Screen i l a sid sd]
>   , hidden   :: [Workspace i l a]   
>   , floating :: M.Map a RationalRect
>   } 



















> --------------------------------------------------------------------
> -- Helper Code
> --------------------------------------------------------------------
> 
> data RationalRect = RationalRect Rational Rational Rational Rational
