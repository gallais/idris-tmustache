module TMustache.Data.DMap

import TMustache.Relation.Order
import public TMustache.Data.TwoThree.Tree

%default total
%access public export

data DMap : (ltR : key -> key -> Type) ->
           (val : key -> Type) -> Type where
  MkDMap : Tree ltR val MInf PInf n -> DMap ltR val

lookup : TotalStrictOrder ltR =>
         (k : key) -> DMap ltR val -> Maybe (val k)
lookup k (MkDMap t) = map getValue $ lookup k LTMInfLift LTLiftPInf t

empty : DMap ltR val
empty = MkDMap (Leaf LTMInfPInf)

update : TotalStrictOrder ltR =>
         (k : key) -> ({k' : key} -> k = k' -> Maybe (val k') -> val k') ->
         DMap ltR val -> DMap ltR val
update k f (MkDMap t) = case update k f LTMInfLift LTLiftPInf t of
  ItFits t'          => MkDMap t'
  TooBig k' v' l' r' => MkDMap (Node2 k' v' l' r')

insert : TotalStrictOrder ltR =>
         (k : key) -> Semigroup (val k) =>
         val k -> DMap ltR val -> DMap ltR val
insert k vk = DMap.update k $ \ eq, mvk1 => case mvk1 of
  Nothing  => rewrite sym eq in vk
  Just vk1 => rewrite sym eq in (rewrite eq in vk1) <+> vk

override : TotalStrictOrder ltR =>
           (k : key) -> val k -> DMap ltR val -> DMap ltR val
override k v = DMap.update k (\ eq, _ => rewrite sym eq in v)

-- Based on @override@ i.e. assuming all keys are distinct
fromList : TotalStrictOrder ltR => List (k : key ** val k) -> DMap ltR val
fromList = foldr (\ (k ** v) => override k v) empty

delete : TotalStrictOrder ltR =>
         (k : key) -> DMap {key} ltR val -> DMap ltR val
delete k (MkDMap t) with (delete k LTMInfLift LTLiftPInf t)
  | SameSize t' = MkDMap t'
  | TooSmall t' = MkDMap t'
