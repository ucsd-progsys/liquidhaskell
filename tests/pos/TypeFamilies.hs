{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module ProxyClass where

import           Data.Proxy
import           GHC.TypeLits (Nat)

type ReadPtrN t  = ReadPtr (t 'Nothing)
newtype ReadPtr a = ReadPtr Int 
data EthernetHeaderBase m = EHB (m ?$ Bytes 6) 
data ForeignPtr a  
newtype Bytes (n :: Nat) = Bytes (ReadPtr Int)

{-@ foo ::  ReadPtrN EthernetHeaderBase @-}
foo ::  ReadPtrN EthernetHeaderBase
foo = undefined 

{-@
data EthernetPacket = EthernetPacket
  { headerEth     :: ReadPtrN EthernetHeaderBase
  }
@-}

data EthernetPacket = EthernetPacket
  { headerEth     :: ReadPtrN EthernetHeaderBase
  }



infixr 1 ?$

type family (?$) (m :: Maybe (* -> *)) (x :: *) :: * where
  'Just f ?$ x = f x
  'Nothing ?$ x = x
