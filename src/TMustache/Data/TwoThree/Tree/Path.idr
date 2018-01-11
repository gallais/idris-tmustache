module TMustache.Data.TwoThree.Tree.Path

import TMustache.Relation.Order

import TMustache.Data.TwoThree.Key
import TMustache.Data.TwoThree.Tree.Type

%default total
%access public export

data Path : Tree ltR val l u n -> (k : key) -> val k -> Type where
  Node2Here   : Path (Node2 k v l r) k v
  Node2Left   : Path l k v -> Path (Node2 k' v' l r) k v
  Node2Right  : Path r k v -> Path (Node2 k' v' l r) k v
  Node3Here1  : Path (Node3 k v k2 v2 l m r) k v
  Node3Here2  : Path (Node3 k1 v1 k v l m r) k v
  Node3Left   : Path l k v -> Path (Node3 k1 v1 k2 v2 l m r) k v
  Node3Middle : Path m k v -> Path (Node3 k1 v1 k2 v2 l m r) k v
  Node3Right  : Path r k v -> Path (Node3 k1 v1 k2 v2 l m r) k v

data Idx : Tree ltR val l u n -> key -> Type where
  MkIdx : {val : key -> Type} -> (v : val k) -> Path t k v -> Idx t k

getValue : {t : Tree ltR val l u n} -> Idx t k -> val k
getValue (MkIdx v _) = v

mapIdx : {t : Tree ltR val l u m} -> {t' : Tree ltR val l' u' m'} ->
         (f : {k : key} -> {v : val k} -> Path t k v -> Path t' k v) ->
         Idx t k -> Idx t' k
mapIdx f (MkIdx v p) = MkIdx v (f p)

lookup : TotalStrictOrder ltR =>
         (k : key) -> ExtendLT ltR l (Lift k) -> ExtendLT ltR (Lift k) u ->
         (t : Tree ltR val l u n) -> Maybe (Idx t k)
lookup {ltR} {n = Z}    k lk ku (Leaf _) = Nothing
lookup {ltR} {n = S n'} k lk ku (Node2 k' v' l r) with (compareBy ltR k k')
  | LT kk' = map (mapIdx Node2Left) $ lookup k lk (LTLift kk') l
  | EQ kk' = Just (rewrite kk' in MkIdx v' Node2Here)
  | GT k'k = map (mapIdx Node2Right) $ lookup k (LTLift k'k) ku r
lookup {ltR} {n = S n'} k lk ku (Node3 k1 v1 k2 v2 l m r) with (compareBy ltR k k1)
  | LT kk1 = map (mapIdx Node3Left) $ lookup k lk (LTLift kk1) l
  | EQ kk1 = Just (rewrite kk1 in MkIdx v1 Node3Here1)
  | GT k1k with (compareBy ltR k k2)
    | LT kk2 = map (mapIdx Node3Middle) $ lookup k (LTLift k1k) (LTLift kk2) m
    | EQ kk2 = Just (rewrite kk2 in MkIdx v2 Node3Here2)
    | GT k2k = map (mapIdx Node3Right) $ lookup k (LTLift k2k) ku r
