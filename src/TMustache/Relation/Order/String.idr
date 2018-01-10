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
  injective = p where postulate p : unpack x = unpack y -> x = y

