module TMustache.Function.Injective

%default total
%access public export

interface Injective (f : a -> b) where

  injective : f x = f y -> x = y
