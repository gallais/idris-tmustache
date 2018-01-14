module TMustache.Data.Map

import TMustache.Relation.Order
import public TMustache.Data.TwoThree.Tree as Tree

%default total
%access public export

data Map : (ltR : key -> key -> Type) ->
           (val : Type) -> Type where
  MkMap : Tree ltR (\ _ => val) MInf PInf n -> Map ltR val

lookup : TotalStrictOrder ltR =>
         key -> Map {key} ltR val -> Maybe val
lookup k (MkMap t) = map getValue' $ lookup k LTMInfLift LTLiftPInf t where

  getValue' : Idx t k -> val
  getValue' (MkIdx _ v _) = v

empty : Map ltR val
empty = MkMap (Leaf LTMInfPInf)

update : TotalStrictOrder ltR =>
         key -> (Maybe val -> val) -> Map {key} ltR val -> Map ltR val
update k f (MkMap t) = case update k (\ _ => f) LTMInfLift LTLiftPInf t of
  ItFits t'          => MkMap t'
  TooBig k' v' l' r' => MkMap (Node2 k' v' l' r')

insert : (TotalStrictOrder ltR, Semigroup val) =>
         key -> val -> Map {key} ltR val -> Map ltR val
insert k v = Map.update k (maybe v (<+> v))

override : TotalStrictOrder ltR =>
           key -> val -> Map {key} ltR val -> Map ltR val
override k v = Map.update k (\ _ => v)

-- Based on @override@ i.e. assuming all keys are distinct
fromList : TotalStrictOrder ltR => List (key, val) -> Map {key} ltR val
fromList = foldr (uncurry override) empty

delete : TotalStrictOrder ltR =>
         key -> Map {key} ltR val -> Map ltR val
delete k (MkMap t) with (delete k LTMInfLift LTLiftPInf t)
  | SameSize t' = MkMap t'
  | TooSmall t' = MkMap t'
