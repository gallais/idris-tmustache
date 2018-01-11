module TMustache.Data.TwoThree.Tree.Type

import TMustache.Data.TwoThree.Key

%default total
%access public export

data Tree : (ltR : key -> key -> Type) ->
            (val : key -> Type) ->
            Extend key -> Extend key -> Nat -> Type where
  Leaf  : ExtendLT ltR l u -> Tree ltR val l u Z
  Node2 : (k : key) -> val k ->
          Tree ltR val l (Lift k) n -> Tree ltR val (Lift k) u n ->
          Tree ltR val l u (S n)
  Node3 : (k1 : key) -> val k1 -> (k2 : key) -> val k2 ->
          Tree ltR val l (Lift k1) n -> Tree ltR val (Lift k1) (Lift k2) n -> Tree ltR val (Lift k2) u n ->
          Tree ltR val l u (S n)

data MayFit : (ltR : key -> key -> Type) ->
              (val : key -> Type) ->
              Extend key -> Extend key -> Nat -> Type where
  ItFits : Tree ltR val l u n -> MayFit ltR val l u n
  TooBig : (k : key) -> val k -> Tree ltR val l (Lift k) n -> Tree ltR val (Lift k) u n -> MayFit ltR val l u n

data Delete : (ltR : key -> key -> Type) ->
              (val : key -> Type) ->
              Extend key -> Extend key -> Nat -> Type where
  SameSize : Tree ltR val l u n -> Delete ltR val l u n
  TooSmall : Tree ltR val l u n -> Delete ltR val l u (S n)
