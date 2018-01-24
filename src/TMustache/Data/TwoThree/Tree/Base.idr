module TMustache.Data.TwoThree.Tree.Base

import TMustache.Relation.Order

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

map : (f : {k : key} -> v k -> w k) -> Tree ltR v l u n -> Tree ltR w l u n
map f (Leaf pr)                 = Leaf pr
map f (Node2 k v l r)           = Node2 k (f v) (map f l) (map f r)
map f (Node3 k1 v1 k2 v2 l m r) = Node3 k1 (f v1) k2 (f v2) (map f l) (map f m) (map f r)

append : StrictOrder ltR => Tree ltR val l a n -> Tree ltR val a u n -> MayFit ltR val l u n
append (Leaf la) (Leaf au) = ItFits (Leaf (transitive la au))
append (Node2 lk lv ll lr) (Node2 rk rv rl rr) with (append lr rl)
  | ItFits lrrl        = ItFits (Node3 lk lv rk rv ll lrrl rr)
  | TooBig k' v' l' r' = TooBig k' v' (Node2 lk lv ll l') (Node2 rk rv r' rr)
append (Node2 lk lv ll lr) (Node3 rk1 rv1 rk2 rv2 rl rm rr) with (append lr rl)
  | ItFits lrrl        = TooBig rk1 rv1 (Node2 lk lv ll lrrl) (Node2 rk2 rv2 rm rr)
  | TooBig k' v' l' r' = TooBig rk1 rv1 (Node3 lk lv k' v' ll l' r') (Node2 rk2 rv2 rm rr)
append (Node3 lk1 lv1 lk2 lv2 ll lm lr) (Node2 rk rv rl rr) with (append lr rl)
  | ItFits lrrl        = TooBig lk2 lv2 (Node2 lk1 lv1 ll lm) (Node2 rk rv lrrl rr)
  | TooBig k' v' l' r' = TooBig lk2 lv2 (Node2 lk1 lv1 ll lm) (Node3 k' v' rk rv l' r' rr)
append (Node3 lk1 lv1 lk2 lv2 ll lm lr) (Node3 rk1 rv1 rk2 rv2 rl rm rr) with (append lr rl)
  | ItFits lrrl        = TooBig lk2 lv2 (Node2 lk1 lv1 ll lm) (Node3 rk1 rv1 rk2 rv2 lrrl rm rr)
  | TooBig k' v' l' r' = TooBig k' v' (Node3 lk1 lv1 lk2 lv2 ll lm l') (Node3 rk1 rv1 rk2 rv2 r' rm rr)
