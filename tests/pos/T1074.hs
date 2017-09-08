-- see https://github.com/ucsd-progsys/liquidhaskell/issues/1074

module Blank where

{-@ type Geq X = {v:Int | X <= v} @-}

{-@ thisOk :: x:Int -> y:{Int | y > 10}  -> () @-}
thisOk :: Int -> Int -> ()
thisOk = undefined

{-@ thisBad1 :: x:Int -> y:Geq y  -> () @-}
thisBad1 :: Int -> Int -> ()
thisBad1 = undefined

{-@ thisBad2 :: x:Int -> y:{y > 10}  -> () @-}
thisBad2 :: Int -> Int -> ()
thisBad2 = undefined

{-@ type NEList a = {xs:[a] | len xs > 0} @-}

{-@ the3 :: Eq a => xs:NEList {x:a | x == headP xs} -> {y:a | headP xs == y} @-}
the3 :: Eq a => [a] -> a
the3 = undefined

{-@ the1 :: Eq a => xs:NEList {x:a | x == headP xs} -> {y:a | headP xs == y} @-}
the1 :: Eq a => [a] -> a
the1 = undefined

{-@ the2 :: Eq a => xs:{v:[{x:a | x == headP xs}] | len v > 0} -> {y:a | headP xs == y} @-}
the2 :: Eq a => [a] -> a
the2 = undefined

{-@ measure headP :: a -> b @-}

Hi everyone,

Its 2017 and it feels odd to send emails cc-ed to 30 people.
Plus, its tedious to copy-paste the 30 addresses.

I made a mailing list so we can just write to a single address.

(I hope everyone gets this ... hmm I guess the only way to
find out is to copy-paste again... curses... foiled again!)

- Ranjit.

Frances Ajo <frances.ajo@gmail.com>,
Heather Oberly <hroberly@gmail.com>,
Ian Silverman <Islander403@hotmail.com>,
Julie Stope <juliej22779@yahoo.com>,
Kamalika Chaudhuri <kamalika@cs.ucsd.edu>,
Kayleigh Gebreselassie <kvondoll@gmail.com>,
Kelly Carll <jones.kellyr@gmail.com>,
Kim Sparrow <kim.sparrow@gmail.com>,
Lauren Zamler <lzamler@gmail.com>,
Lisa Starace <lisa.a.starace@gmail.com>,
Mike DeEmedio <deemedio32@yahoo.com>,
Morgan Craft <craft.morganc@gmail.com>,
Rachel Jensen <racheljensen@hotmail.com>,
Ranjit Jhala <jhala@cs.ucsd.edu>,
Sarah Thomas <sapsel@gmail.com>,
Scott Armstrong <sjordan72@gmail.com>,
Tony Winney <twinney@gmail.com>
