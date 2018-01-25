module TMustache.Relation.Order.String

import TMustache.Function.Injective
import TMustache.Relation.Order
import TMustache.Relation.Order.On
import TMustache.Relation.Order.Char
import TMustache.Relation.Order.Lexicographic

%default total
%access public export

StringLT : String -> String -> Type
StringLT = OnLT (LexicoLT CharLT)

implementation Injection String (List Char) where

  injection = unpack
  injective {x} {y} eq = aux (unpack x) (unpack y) x y eq where

    aux : (x, y : List Char) -> (c, d : String) -> x = y -> c = d
    aux x x c d Refl = believe_me (the (c = c) Refl)
