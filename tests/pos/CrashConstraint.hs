module FOO () where

mkSessData :: TcpEndPoint -> Bool 
mkSessData x = isSrcTCP x

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

safeSimplifyPatTuple :: RewriteRule
safeSimplifyPatTuple e 
  = find ((CoreUtils.exprType e ==) . CoreUtils.exprType) (simplifyPatTuple e)  
