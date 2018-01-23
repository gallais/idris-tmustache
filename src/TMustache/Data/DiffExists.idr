module TMustache.Data.DiffExists

%default total
%access public export

record DiffExists (idx : Type) (t : idx -> idx -> Type) where
  constructor MkDiffExists
  index : idx -> idx
  value : (i : idx) -> t i (index i)

combine : ({a, b, c : idx} -> h a b -> t b c -> t a c) ->
          DiffExists idx h -> DiffExists idx t -> DiffExists idx t
combine c (MkDiffExists f h) (MkDiffExists g t) = MkDiffExists (g . f) (\ i => c (h i) (t (f i)))
