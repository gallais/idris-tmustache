module TMustache.Data.Star

%default total
%access public export

data Star : (t : a -> a -> Type) -> a -> a -> Type where
  Nil  : Star t a a
  (::) : t a b -> Star t b c -> Star t a c


map : ({a, b : idx} -> t a b -> u a b) -> Star t a b -> Star u a b
map f []          = []
map f (st :: sts) = f st :: map f sts
