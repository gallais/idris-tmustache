module TMustache.Data.Map

import TMustache.Relation.Order
import TMustache.Data.TwoThree.Key
import TMustache.Data.TwoThree.Tree.Internal as Tree

%default total
%access public export

data Map : (ltR : key -> key -> Type) ->
           (val : key -> Type) -> Type where
  MkMap : Tree ltR val MInf PInf n -> Map ltR val

lookup : TotalStrictOrder ltR =>
         (k : key) -> Map ltR val -> Maybe (val k)
lookup k (MkMap t) = map getValue $ Tree.lookup k LTMInfLift LTLiftPInf t

empty : Map ltR val
empty = MkMap (Leaf LTMInfPInf)

insert : TotalStrictOrder ltR =>
         (k : key) -> Semigroup (val k) =>
         val k -> Map ltR val -> Map ltR val
insert k v (MkMap t) with (Tree.insert k v LTMInfLift LTLiftPInf t)
  | ItFits t'          = MkMap t'
  | TooBig k' v' l' r' = MkMap (Node2 k' v' l' r')

delete : TotalStrictOrder ltR =>
         (k : key) -> Map {key} ltR val -> Map ltR val
delete k (MkMap t) with (Tree.delete k LTMInfLift LTLiftPInf t)
  | SameSize t' = MkMap t'
  | TooSmall t' = MkMap t'
