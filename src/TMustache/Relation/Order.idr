module TMustache.Relation.Order

%default total
%access public export

interface StrictOrder (lt : a -> a -> Type) where

  irreflexive : lt x x -> Void
  transitive  : lt x y -> lt y z -> lt x z

data Trichotomy : (lta : a -> a -> Type) -> a -> a -> Type where
  LT : lta x y -> Trichotomy lta x y
  EQ : x = y   -> Trichotomy lta x y
  GT : lta y x -> Trichotomy lta x y

interface StrictOrder lt =>
          TotalStrictOrder (lt : a -> a -> Type) where

  trichotomy : (x, y : a) -> Trichotomy lt x y


ymotohcirt : Trichotomy lt x y -> Trichotomy lt y x
ymotohcirt (LT pr) = GT pr
ymotohcirt (EQ eq) = EQ $ sym eq
ymotohcirt (GT pr) = LT pr
