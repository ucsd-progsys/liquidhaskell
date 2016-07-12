module DependeTypes where



data MI s
  = Small { mi_input :: String  }


{-@ Small :: forall s. {v:String | s == v } -> MI s @-}
