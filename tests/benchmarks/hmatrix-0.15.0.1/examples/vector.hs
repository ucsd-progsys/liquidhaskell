-- conversion to/from Data.Vector.Storable
-- from Roman Leshchinskiy "vector" package
--
-- In the future Data.Packed.Vector will be replaced by Data.Vector.Storable

-------------------------------------------

import Numeric.LinearAlgebra as H
import Data.Packed.Development(unsafeFromForeignPtr, unsafeToForeignPtr)
import Foreign.Storable
import qualified Data.Vector.Storable as V

fromVector :: Storable t => V.Vector t -> H.Vector t
fromVector v = unsafeFromForeignPtr p i n where
    (p,i,n) = V.unsafeToForeignPtr v

toVector :: Storable t => H.Vector t -> V.Vector t
toVector v = V.unsafeFromForeignPtr p i n where
    (p,i,n) = unsafeToForeignPtr v

-------------------------------------------

v = V.slice 5 10 (V.fromList [1 .. 10::Double] V.++ V.replicate 10 7)

w = subVector 2 3 (linspace 5 (0,1)) :: Vector Double

main = do
    print v
    print $ fromVector v
    print w
    print $ toVector w
