module TMustache.Data.TwoThree.Key

import TMustache.Relation.Order

%default total
%access public export

data Extend : Type -> Type where
  MInf : Extend key
  Lift : key -> Extend key
  PInf : Extend key

data ExtendLT : (ltR : key -> key -> Type) -> 
                Extend key -> Extend key -> Type where
  LTMInfPInf : ExtendLT ltR MInf PInf
  LTMInfLift : ExtendLT ltR MInf (Lift y)
  LTLift     : ltR x y -> ExtendLT ltR (Lift x) (Lift y)
  LTLiftPInf : ExtendLT ltR (Lift x) PInf

implementation Uninhabited (ExtendLT ltR PInf x) where uninhabited prf impossible
implementation Uninhabited (ExtendLT ltR x MInf) where uninhabited prf impossible
implementation Uninhabited (ltR x y) =>
               Uninhabited (ExtendLT ltR (Lift x) (Lift y)) where
  uninhabited (LTLift prf) = uninhabited prf

implementation StrictOrder ltR => StrictOrder (ExtendLT ltR) where

  irreflexive (LTLift prf) = irreflexive prf

  transitive LTMInfPInf q = absurd q
  transitive LTLiftPInf q = absurd q
  transitive p LTMInfPInf = absurd p
  transitive p LTMInfLift = absurd p
  transitive LTMInfLift LTLiftPInf = LTMInfPInf
  transitive LTMInfLift (LTLift _) = LTMInfLift
  transitive (LTLift _) LTLiftPInf = LTLiftPInf
  transitive (LTLift p) (LTLift q) = LTLift (transitive p q)

trichotomyMInf : (x : Extend key) -> Trichotomy (ExtendLT ltR) MInf x
trichotomyMInf MInf     = EQ Refl
trichotomyMInf (Lift _) = LT LTMInfLift
trichotomyMInf PInf     = LT LTMInfPInf

trichotomyPInf : (x : Extend key) -> Trichotomy (ExtendLT ltR) x PInf
trichotomyPInf MInf     = LT LTMInfPInf
trichotomyPInf (Lift _) = LT LTLiftPInf
trichotomyPInf PInf     = EQ Refl

implementation TotalStrictOrder ltR => TotalStrictOrder (ExtendLT ltR) where

  trichotomy MInf q = trichotomyMInf q
  trichotomy p MInf = ymotohcirt (trichotomyMInf p)
  trichotomy p PInf = trichotomyPInf p
  trichotomy PInf q = ymotohcirt (trichotomyPInf q)
  trichotomy (Lift p) (Lift q) with (the (Trichotomy ltR p q) (trichotomy p q)) 
    | LT pr = LT (LTLift pr)
    | EQ eq = EQ (cong eq)
    | GT pr = GT (LTLift pr)
