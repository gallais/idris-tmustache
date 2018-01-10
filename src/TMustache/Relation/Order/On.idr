module TMustache.Relation.Order.On

import TMustache.Function.Injective
import TMustache.Relation.Order

%default total
%access public export

data OnLT : (ltR : b -> b -> Type) -> (f : a -> b) -> a -> a -> Type where
  MkOnLT : ltR (f x) (f y) -> OnLT ltR f x y

implementation StrictOrder ltR => StrictOrder (OnLT ltR f) where

  irreflexive (MkOnLT p) = irreflexive p

  transitive (MkOnLT p) (MkOnLT q) = MkOnLT (transitive p q)

implementation (TotalStrictOrder ltR, Injective fn) =>
               TotalStrictOrder (OnLT ltR fn) where

  trichotomy x y with (the (Trichotomy ltR (fn x) (fn y)) (trichotomy (fn x) (fn y)))
    | LT ltfxfy = LT (MkOnLT ltfxfy)
    | EQ eqfxfy = EQ (injective eqfxfy)
    | GT ltfyfx = GT (MkOnLT ltfyfx)
