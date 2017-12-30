module TMustache.Data.Set

import TMustache.Relation.Order
import TMustache.Data.Map as Map

%default total
%access public export

implementation Semigroup () where _ <+> _ = ()

data Set : (key : Type) -> (ltR : key -> key -> Type) -> Type where
  MkSet : Map key ltR (\ _ => ()) -> Set key ltR

empty : Set key ltR
empty = MkSet Map.empty

insert : TotalStrictOrder ltR => 
         (k : key) -> Set key ltR -> Set key ltR
insert k (MkSet s) = MkSet (Map.insert k () s)

fromList : TotalStrictOrder ltR =>
           List key -> Set key ltR
fromList = foldr insert empty

delete : TotalStrictOrder ltR =>
         (k : key) -> Set key ltR -> Set key ltR
delete k (MkSet s) = MkSet (Map.delete k s)

