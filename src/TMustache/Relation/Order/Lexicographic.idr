module TMustache.Relation.Order.Lexicographic

import TMustache.Relation.Order

%default total
%access public export

data LexicoLT : (ltR : a -> a -> Type) -> List a -> List a -> Type where
  NilConsLT : LexicoLT ltR [] (x :: xs)
  HeadLT    : ltR x y -> LexicoLT ltR (x :: xs) (y :: ys)
  TailLT    : LexicoLT ltR xs ys -> LexicoLT ltR (x :: xs) (x :: ys)

implementation StrictOrder ltR => StrictOrder (LexicoLT ltR) where

  irreflexive (HeadLT pr) = irreflexive pr
  irreflexive (TailLT pr) = irreflexive pr

  transitive NilConsLT  (HeadLT _) = NilConsLT
  transitive NilConsLT  (TailLT _) = NilConsLT
  transitive (HeadLT p) (HeadLT q) = HeadLT (transitive p q)
  transitive (HeadLT p) (TailLT q) = HeadLT p
  transitive (TailLT p) (HeadLT q) = HeadLT q
  transitive (TailLT p) (TailLT q) = TailLT (transitive p q)

implementation TotalStrictOrder ltR => TotalStrictOrder (LexicoLT ltR) where

  trichotomy []        []        = EQ Refl
  trichotomy []        (_ :: _)  = LT NilConsLT
  trichotomy (_ :: _)  []        = GT NilConsLT
  trichotomy (x :: xs) (y :: ys) with (the (Trichotomy ltR x y) (trichotomy x y))
    trichotomy (x :: xs) (y :: ys) | LT ltxy = LT (HeadLT ltxy)
    trichotomy (x :: xs) (y :: ys) | GT ltyx = GT (HeadLT ltyx)
    trichotomy (x :: xs) (x :: ys) | EQ Refl with (the (Trichotomy (LexicoLT ltR) xs ys) (trichotomy xs ys))
      | LT ltxsys = LT (TailLT ltxsys)
      | EQ eqxsys = EQ (cong eqxsys)
      | GT ltysxs = GT (TailLT ltysxs)
