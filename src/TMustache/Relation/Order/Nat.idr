module TMustache.Relation.Order.Nat

import TMustache.Relation.Order

%default total
%access public export

data NatLT : Nat -> Nat -> Type where
  ZSLT : NatLT Z (S n)
  SSLT : NatLT m n -> NatLT (S m) (S n)

implementation StrictOrder NatLT where

  irreflexive (SSLT p) = irreflexive p

  transitive ZSLT     (SSLT p) = ZSLT
  transitive (SSLT p) (SSLT q) = SSLT (transitive p q)

implementation TotalStrictOrder NatLT where

  trichotomy Z     Z     = EQ Refl
  trichotomy Z     (S n) = LT ZSLT
  trichotomy (S m) Z     = GT ZSLT
  trichotomy (S m) (S n) with (the (Trichotomy NatLT m n) (trichotomy m n))
    | LT ltmn = LT (SSLT ltmn)
    | EQ eqmn = EQ (cong eqmn)
    | GT ltnm = GT (SSLT ltnm)
