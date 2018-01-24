module TMustache.Data.TwoThree.Tree.Insert

import TMustache.Relation.Order

import TMustache.Data.TwoThree.Key
import TMustache.Data.TwoThree.Tree.Base

%default total
%access public export

update : TotalStrictOrder ltR =>
         (k : key) -> ({k1 : key} -> k = k1 -> Maybe (val k1) -> val k1) ->
	 ExtendLT ltR l (Lift k) -> ExtendLT ltR (Lift k) u ->
         Tree ltR val l u n -> MayFit ltR val l u n
update k f lk ku (Leaf _) = TooBig k (f Refl Nothing) (Leaf lk) (Leaf ku)
update k f lk ku (Node2 k1 v1 l r) with (compareBy ltR k k1)
  | EQ kk1 = ItFits (Node2 k1 (f kk1 (Just v1)) l r)
  | LT kk1  with (update k f lk (LTLift kk1) l)
    | ItFits t           = ItFits (Node2 k1 v1 t r)
    | TooBig k' v' ll lr = ItFits (Node3 k' v' k1 v1 ll lr r)
  | GT k1k  with (update k f (LTLift k1k) ku r)
    | ItFits t           = ItFits (Node2 k1 v1 l t)
    | TooBig k' v' rl rr = ItFits (Node3 k1 v1 k' v' l rl rr)
update k f lk ku (Node3 k1 v1 k2 v2 l m r) with (compareBy ltR k k1)
  | EQ kk1 = ItFits (Node3 k1 (f kk1 (Just v1)) k2 v2 l m r)
  | LT kk1 with (update k f lk (LTLift kk1) l)
     | ItFits t           = ItFits (Node3 k1 v1 k2 v2 t m r)
     | TooBig k' v' ll lr = TooBig k1 v1 (Node2 k' v' ll lr) (Node2 k2 v2 m r)
  | GT k1k with (compareBy ltR k k2)
     | EQ kk2 = ItFits (Node3 k1 v1 k2 (f kk2 (Just v2)) l m r)
     | LT kk2 with (update k f (LTLift k1k) (LTLift kk2) m)
       | ItFits t           = ItFits (Node3 k1 v1 k2 v2 l t r)
       | TooBig k' v' ml mr = TooBig k' v' (Node2 k1 v1 l ml) (Node2 k2 v2 mr r)
     | GT k2k with (update k f (LTLift k2k) ku r)
       | ItFits t           = ItFits (Node3 k1 v1 k2 v2 l m t)
       | TooBig k' v' rl rr = TooBig k2 v2 (Node2 k1 v1 l m) (Node2 k' v' rl rr)
