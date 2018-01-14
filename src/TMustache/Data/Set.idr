module TMustache.Data.Set

import TMustache.Relation.Order
import public TMustache.Data.Map as Map

%default total
%access public export

data Set : (ltR : key -> key -> Type) -> Type where
  MkSet : Map ltR (\ _ => ()) -> Set ltR

elem : TotalStrictOrder ltR =>
       (k : key) -> Set {key} ltR -> Bool
elem k (MkSet s) = isJust $ Map.lookup k s

empty : Set ltR
empty = MkSet Map.empty

insert : TotalStrictOrder ltR => 
         (k : key) -> Set {key} ltR -> Set ltR
insert k (MkSet s) = MkSet (Map.override k () s)

fromList : TotalStrictOrder ltR =>
           List key -> Set {key} ltR
fromList = foldr insert empty

delete : TotalStrictOrder ltR =>
         (k : key) -> Set {key} ltR -> Set {key} ltR
delete k (MkSet s) = MkSet (Map.delete k s)

