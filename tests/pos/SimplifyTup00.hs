
-- See: https://github.com/ucsd-progsys/liquidhaskell/pull/752

module FOO (mkSessData) where

mkSessData :: TcpEndPoint -> Bool
mkSessData = isSrcTCP

{- With the safeSimplifyPatTuple rewrite rule,
   the body of the below expression become a
   case with type (Port, Port) because the
   case is becoming the outer-most
   body expression
-}

isSrcTCP :: TcpEndPoint -> Bool
isSrcTCP x = (addrTE x, portTE x) == (srcIP, srcPort)
 where
   (PP (PortId srcIP _) (PortId srcPort _)) = idTCP x


data TCPId = PP PortId PortId
data PortId = PortId Port Port

data TcpEndPoint = TcpEndPoint { addrTE :: Port, portTE :: Port }


data Port = P deriving (Eq)

idTCP :: TcpEndPoint -> TCPId --  (PortId, PortId)
idTCP tcp = undefined
