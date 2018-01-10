module TMustache.Relation.Order.Char

import TMustache.Function.Injective
import TMustache.Relation.Order
import TMustache.Relation.Order.On
import TMustache.Relation.Order.Nat

%default total
%access public export

CharLT : Char -> Char -> Type
CharLT = OnLT NatLT

implementation Injection Char Nat where

  injection = toNat
  injective = p where postulate p : {x, y : Char} -> toNat x = toNat y -> x = y

