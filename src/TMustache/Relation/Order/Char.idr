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
  injective {x} {y} eq = aux (toNat x) (toNat y) x y eq where

    aux : (x, y : Nat) -> (c, d : Char) -> x = y -> c = d
    aux x x c d Refl = believe_me (the (c = c) Refl)
