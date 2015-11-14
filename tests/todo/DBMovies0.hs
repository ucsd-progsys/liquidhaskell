module MovieClient where


data Tag 
data Value


type Table t v = [Dict t v]

data Dict key val = D {ddom :: [key], dfun :: key -> val}


{-@ fromList :: forall <range :: key -> val -> Prop, p :: Dict key val -> Prop>.
                x:[Dict <range> key val <<p>>] -> {v:[Dict <range> key val <<p>>] | x = v}
  @-}
fromList :: [Dict key val] -> Table key val
fromList xs = xs


{-@ data Dict key val <range :: key -> val -> Prop>
  = D ( ddom :: [key])
      ( dfun :: i:key -> val<range i>)
  @-}


{-@ type Movies      = [MovieScheme] @-}
{-@ type MovieScheme = {v:Dict <{\t val -> (t ~~ "year")}> Tag Value | true } @-}

type Movies    = Table Tag Value

movies :: Movies
{-@ movies :: Movies @-}
movies = fromList []

y = "year"