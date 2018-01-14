module TMustache.Data.Map

import TMustache.Relation.Order
import public TMustache.Data.TwoThree.Tree

%default total
%access public export

data Map : (ltR : key -> key -> Type) ->
           (val : key -> Type) -> Type where
  MkMap : Tree ltR val MInf PInf n -> Map ltR val

lookup : TotalStrictOrder ltR =>
         (k : key) -> Map ltR val -> Maybe (val k)
lookup k (MkMap t) = map getValue $ lookup k LTMInfLift LTLiftPInf t

empty : Map ltR val
empty = MkMap (Leaf LTMInfPInf)

update : TotalStrictOrder ltR =>
         (k : key) -> ({k' : key} -> k = k' -> Maybe (val k') -> val k') ->
         Map ltR val -> Map ltR val
update k f (MkMap t) = case update k f LTMInfLift LTLiftPInf t of
  ItFits t'          => MkMap t'
  TooBig k' v' l' r' => MkMap (Node2 k' v' l' r')

insert : TotalStrictOrder ltR =>
         (k : key) -> Semigroup (val k) =>
         val k -> Map ltR val -> Map ltR val
insert k vk = Map.update k $ \ eq, mvk1 => case mvk1 of
  Nothing  => rewrite sym eq in vk
  Just vk1 => rewrite sym eq in (rewrite eq in vk1) <+> vk

override : TotalStrictOrder ltR =>
           (k : key) -> val k -> Map ltR val -> Map ltR val
override k v = Map.update k (\ eq, _ => rewrite sym eq in v)

-- Based on @override@ i.e. assuming all keys are distinct
fromList : TotalStrictOrder ltR => List (k : key ** val k) -> Map ltR val
fromList = foldr (\ (k ** v) => override k v) empty

delete : TotalStrictOrder ltR =>
         (k : key) -> Map {key} ltR val -> Map ltR val
delete k (MkMap t) with (delete k LTMInfLift LTLiftPInf t)
  | SameSize t' = MkMap t'
  | TooSmall t' = MkMap t'
