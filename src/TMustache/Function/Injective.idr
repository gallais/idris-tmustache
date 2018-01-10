module TMustache.Function.Injective

%default total
%access public export

interface Injection a b | a where
  injection : a -> b
  injective : injection x = injection y -> x = y

