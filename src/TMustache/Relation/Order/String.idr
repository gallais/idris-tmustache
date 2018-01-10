module TMustache.Relation.Order.String

import Prelude.Strings as PS

import TMustache.Function.Injective
import TMustache.Relation.Order
import TMustache.Relation.Order.On
import TMustache.Relation.Order.Char
import TMustache.Relation.Order.Lexicographic

%default total
%access public export

StringLT : String -> String -> Type
StringLT = OnLT (LexicoLT CharLT) PS.unpack

[unpackInj] Injective PS.unpack where

  injective = p where postulate p : unpack str = unpack str' -> str = str'

