module TMustache.Data.TwoThree.Tree.Insert

import TMustache.Relation.Order

import TMustache.Data.TwoThree.Key
import TMustache.Data.TwoThree.Tree.Type

%default total
%access public export

insert : TotalStrictOrder ltR =>
         (k : key) -> val k ->
         Semigroup (val k) =>
         ExtendLT ltR l (Lift k) -> ExtendLT ltR (Lift k) u ->
         Tree ltR val l u n -> MayFit ltR val l u n
insert k v lk ku (Leaf _) = TooBig k v (Leaf lk) (Leaf ku)
insert k v lk ku (Node2 k1 v1 l r) with (the (Trichotomy ltR k k1) (trichotomy k k1))
  | EQ kk1 = ItFits (Node2 k ((rewrite kk1 in v1) <+> v) (rewrite kk1 in l) (rewrite kk1 in r))
  | LT kk1  with (insert k v lk (LTLift kk1) l)
    | ItFits t           = ItFits (Node2 k1 v1 t r)
    | TooBig k' v' ll lr = ItFits (Node3 k' v' k1 v1 ll lr r)
  | GT k1k  with (insert k v (LTLift k1k) ku r)
    | ItFits t           = ItFits (Node2 k1 v1 l t)
    | TooBig k' v' rl rr = ItFits (Node3 k1 v1 k' v' l rl rr)
insert k v lk ku (Node3 k1 v1 k2 v2 l m r) with (the (Trichotomy ltR k k1) (trichotomy k k1))
  | EQ kk1 = ItFits (Node3 k ((rewrite kk1 in v1) <+> v) k2 v2 (rewrite kk1 in l) (rewrite kk1 in m) r)
  | LT kk1 with (insert k v lk (LTLift kk1) l)
     | ItFits t           = ItFits (Node3 k1 v1 k2 v2 t m r)
     | TooBig k' v' ll lr = TooBig k1 v1 (Node2 k' v' ll lr) (Node2 k2 v2 m r)
  | GT k1k with (the (Trichotomy ltR k k2) (trichotomy k k2))
     | EQ kk2 = ItFits (Node3 k1 v1 k ((rewrite kk2 in v2) <+> v) l (rewrite kk2 in m) (rewrite kk2 in r))
     | LT kk2 with (insert k v (LTLift k1k) (LTLift kk2) m)
       | ItFits t           = ItFits (Node3 k1 v1 k2 v2 l t r)
       | TooBig k' v' ml mr = TooBig k' v' (Node2 k1 v1 l ml) (Node2 k2 v2 mr r)
     | GT k2k with (insert k v (LTLift k2k) ku r)
       | ItFits t           = ItFits (Node3 k1 v1 k2 v2 l m t)
       | TooBig k' v' rl rr = TooBig k2 v2 (Node2 k1 v1 l m) (Node2 k' v' rl rr)

