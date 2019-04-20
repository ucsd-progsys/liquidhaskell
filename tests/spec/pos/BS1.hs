
import Data.ByteString.Lazy as LB


foo z = LB.pack z

{-@ bar :: _ -> {v:_ | v >= 0} @-}
bar z = LB.length z

