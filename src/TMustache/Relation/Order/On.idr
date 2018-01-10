module TMustache.Relation.Order.On

import TMustache.Function.Injective
import TMustache.Relation.Order

%default total
%access public export

data OnLT : (ltR : b -> b -> Type) -> a -> a -> Type where
  MkOnLT : {x, y : a} -> Injection a b => ltR (injection x) (injection y) -> OnLT ltR x y

implementation StrictOrder ltR => StrictOrder (OnLT ltR) where

  irreflexive (MkOnLT p) = irreflexive p

  transitive (MkOnLT p) (MkOnLT q) = MkOnLT (transitive p q)

implementation (TotalStrictOrder ltR, Injection a b) =>
               TotalStrictOrder (OnLT {a} {b} ltR) where

  trichotomy x y with (trichotomy {lt = ltR} (injection x) (injection y))
    | LT ltfxfy = LT (MkOnLT ltfxfy)
    | EQ eqfxfy = EQ (injective eqfxfy)
    | GT ltfyfx = GT (MkOnLT ltfyfx)
