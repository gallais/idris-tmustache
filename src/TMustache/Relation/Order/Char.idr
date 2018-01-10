module TMustache.Relation.Order.Char

import TMustache.Function.Injective
import TMustache.Relation.Order
import TMustache.Relation.Order.On
import TMustache.Relation.Order.Nat

%default total
%access public export

charToNat : Char -> Nat
charToNat = toNat

CharLT : Char -> Char -> Type
CharLT = OnLT NatLT charToNat

[charToNatInj] Injective Char.charToNat where

  injective = p
    where postulate p : charToNat x = charToNat y -> x = y

