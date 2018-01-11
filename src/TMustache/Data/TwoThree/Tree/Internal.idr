module TMustache.Data.TwoThree.Tree.Internal

import public TMustache.Data.TwoThree.Key
import TMustache.Relation.Order

%default total
%access public export

data Tree : (ltR : key -> key -> Type) ->
            (val : key -> Type) ->
            Extend key -> Extend key -> Nat -> Type where
  Leaf  : ExtendLT ltR l u -> Tree ltR val l u Z
  Node2 : (k : key) -> val k ->
          Tree ltR val l (Lift k) n -> Tree ltR val (Lift k) u n ->
          Tree ltR val l u (S n)
  Node3 : (k1 : key) -> val k1 -> (k2 : key) -> val k2 ->
          Tree ltR val l (Lift k1) n -> Tree ltR val (Lift k1) (Lift k2) n -> Tree ltR val (Lift k2) u n ->
          Tree ltR val l u (S n)

data Path : Tree ltR val l u n -> (k : key) -> val k -> Type where
  Node2Here   : Path (Node2 k v l r) k v
  Node2Left   : Path l k v -> Path (Node2 k' v' l r) k v
  Node2Right  : Path r k v -> Path (Node2 k' v' l r) k v
  Node3Here1  : Path (Node3 k v k2 v2 l m r) k v
  Node3Here2  : Path (Node3 k1 v1 k v l m r) k v
  Node3Left   : Path l k v -> Path (Node3 k1 v1 k2 v2 l m r) k v
  Node3Middle : Path m k v -> Path (Node3 k1 v1 k2 v2 l m r) k v
  Node3Right  : Path r k v -> Path (Node3 k1 v1 k2 v2 l m r) k v

data Idx : Tree ltR val l u n -> key -> Type where
  MkIdx : {val : key -> Type} -> (v : val k) -> Path t k v -> Idx t k

getValue : {t : Tree ltR val l u n} -> Idx t k -> val k
getValue (MkIdx v _) = v

mapIdx : {t : Tree ltR val l u m} -> {t' : Tree ltR val l' u' m'} ->
         (f : {k : key} -> {v : val k} -> Path t k v -> Path t' k v) ->
         Idx t k -> Idx t' k
mapIdx f (MkIdx v p) = MkIdx v (f p)

map : (f : {k : key} -> v k -> w k) -> Tree ltR v l u n -> Tree ltR w l u n
map f (Leaf pr)                 = Leaf pr
map f (Node2 k v l r)           = Node2 k (f v) (map f l) (map f r)
map f (Node3 k1 v1 k2 v2 l m r) = Node3 k1 (f v1) k2 (f v2) (map f l) (map f m) (map f r)

lookup : TotalStrictOrder ltR =>
         (k : key) -> ExtendLT ltR l (Lift k) -> ExtendLT ltR (Lift k) u ->
         (t : Tree ltR val l u n) -> Maybe (Idx t k)
lookup {ltR} {n = Z}    k lk ku (Leaf _) = Nothing
lookup {ltR} {n = S n'} k lk ku (Node2 k' v' l r) with (the (Trichotomy ltR k k') (trichotomy k k'))
  | LT kk' = map (mapIdx Node2Left) $ lookup k lk (LTLift kk') l
  lookup k lk ku (Node2 k v' l r) | EQ Refl = Just (MkIdx v' Node2Here)
  | GT k'k = map (mapIdx Node2Right) $ lookup k (LTLift k'k) ku r
lookup {ltR} {n = S n'} k lk ku (Node3 k1 v1 k2 v2 l m r) with (the (Trichotomy ltR k k1) (trichotomy k k1))
  | LT kk1 = map (mapIdx Node3Left) $ lookup k lk (LTLift kk1) l
  lookup k lk ku (Node3 k v1 k2 v2 l m r) | EQ Refl = Just (MkIdx v1 Node3Here1)
  | GT k1k with (the (Trichotomy ltR k k2) (trichotomy k k2))
    | LT kk2 = map (mapIdx Node3Middle) $ lookup k (LTLift k1k) (LTLift kk2) m
    lookup k lk ku (Node3 k1 v1 k v2 l m r) | GT k1k | EQ Refl = Just (MkIdx v2 Node3Here2)
    | GT k2k = map (mapIdx Node3Right) $ lookup k (LTLift k2k) ku r

data MayFit : (ltR : key -> key -> Type) ->
              (val : key -> Type) ->
              Extend key -> Extend key -> Nat -> Type where
  ItFits : Tree ltR val l u n -> MayFit ltR val l u n
  TooBig : (k : key) -> val k -> Tree ltR val l (Lift k) n -> Tree ltR val (Lift k) u n -> MayFit ltR val l u n

insert : TotalStrictOrder ltR =>
         (k : key) -> val k ->
         Semigroup (val k) =>
         ExtendLT ltR l (Lift k) -> ExtendLT ltR (Lift k) u ->
         Tree ltR val l u n -> MayFit ltR val l u n
insert k v lk ku (Leaf _) = TooBig k v (Leaf lk) (Leaf ku)
insert k v lk ku (Node2 k1 v1 l r) with (the (Trichotomy ltR k k1) (trichotomy k k1))
  | EQ kk1 = ItFits (Node2 k ((rewrite kk1 in v1) <+> v) (rewrite kk1 in l) (rewrite kk1 in r))
  | LT kk1  with (insert k v lk (LTLift kk1) l)
    | ItFits t           = ItFits (Node2 k1 v1 t r)
    | TooBig k' v' ll lr = ItFits (Node3 k' v' k1 v1 ll lr r)
  | GT k1k  with (insert k v (LTLift k1k) ku r)
    | ItFits t           = ItFits (Node2 k1 v1 l t)
    | TooBig k' v' rl rr = ItFits (Node3 k1 v1 k' v' l rl rr)
insert k v lk ku (Node3 k1 v1 k2 v2 l m r) with (the (Trichotomy ltR k k1) (trichotomy k k1))
  | EQ kk1 = ItFits (Node3 k ((rewrite kk1 in v1) <+> v) k2 v2 (rewrite kk1 in l) (rewrite kk1 in m) r)
  | LT kk1 with (insert k v lk (LTLift kk1) l)
     | ItFits t           = ItFits (Node3 k1 v1 k2 v2 t m r)
     | TooBig k' v' ll lr = TooBig k1 v1 (Node2 k' v' ll lr) (Node2 k2 v2 m r)
  | GT k1k with (the (Trichotomy ltR k k2) (trichotomy k k2))
     | EQ kk2 = ItFits (Node3 k1 v1 k ((rewrite kk2 in v2) <+> v) l (rewrite kk2 in m) (rewrite kk2 in r))
     | LT kk2 with (insert k v (LTLift k1k) (LTLift kk2) m)
       | ItFits t           = ItFits (Node3 k1 v1 k2 v2 l t r)
       | TooBig k' v' ml mr = TooBig k' v' (Node2 k1 v1 l ml) (Node2 k2 v2 mr r)
     | GT k2k with (insert k v (LTLift k2k) ku r)
       | ItFits t           = ItFits (Node3 k1 v1 k2 v2 l m t)
       | TooBig k' v' rl rr = TooBig k2 v2 (Node2 k1 v1 l m) (Node2 k' v' rl rr)

append : StrictOrder ltR => Tree ltR val l a n -> Tree ltR val a u n -> MayFit ltR val l u n
append (Leaf la) (Leaf au) = ItFits (Leaf (transitive la au))
append (Node2 lk lv ll lr) (Node2 rk rv rl rr) with (append lr rl)
  | ItFits lrrl        = ItFits (Node3 lk lv rk rv ll lrrl rr)
  | TooBig k' v' l' r' = TooBig k' v' (Node2 lk lv ll l') (Node2 rk rv r' rr)
append (Node2 lk lv ll lr) (Node3 rk1 rv1 rk2 rv2 rl rm rr) with (append lr rl)
  | ItFits lrrl        = TooBig rk1 rv1 (Node2 lk lv ll lrrl) (Node2 rk2 rv2 rm rr)
  | TooBig k' v' l' r' = TooBig rk1 rv1 (Node3 lk lv k' v' ll l' r') (Node2 rk2 rv2 rm rr)
append (Node3 lk1 lv1 lk2 lv2 ll lm lr) (Node2 rk rv rl rr) with (append lr rl)
  | ItFits lrrl        = TooBig lk2 lv2 (Node2 lk1 lv1 ll lm) (Node2 rk rv lrrl rr)
  | TooBig k' v' l' r' = TooBig lk2 lv2 (Node2 lk1 lv1 ll lm) (Node3 k' v' rk rv l' r' rr)
append (Node3 lk1 lv1 lk2 lv2 ll lm lr) (Node3 rk1 rv1 rk2 rv2 rl rm rr) with (append lr rl)
  | ItFits lrrl        = TooBig lk2 lv2 (Node2 lk1 lv1 ll lm) (Node3 rk1 rv1 rk2 rv2 lrrl rm rr)
  | TooBig k' v' l' r' = TooBig k' v' (Node3 lk1 lv1 lk2 lv2 ll lm l') (Node3 rk1 rv1 rk2 rv2 r' rm rr)


data Delete : (ltR : key -> key -> Type) ->
              (val : key -> Type) ->
              Extend key -> Extend key -> Nat -> Type where
  SameSize : Tree ltR val l u n -> Delete ltR val l u n
  TooSmall : Tree ltR val l u n -> Delete ltR val l u (S n)

delete : TotalStrictOrder ltR =>
         (k : key) ->
         ExtendLT ltR l (Lift k) -> ExtendLT ltR (Lift k) u ->
         Tree ltR val l u n -> Delete ltR val l u n
delete k lk ku (Leaf prf) = SameSize (Leaf prf)
delete k lk ku (Node2 k1 v1 l r) with (the (Trichotomy ltR k k1) (trichotomy k k1))
  delete k lk ku (Node2 k1 v1 l r) | LT kk1 with (delete k lk (LTLift kk1) l)
    | SameSize l' = SameSize (Node2 k1 v1 l' r)
    | TooSmall l' = case r of
        Node2 rk rv rl rr              => TooSmall (Node3 k1 v1 rk rv l' rl rr)
        Node3 rk1 rv1 rk2 rv2 rl rm rr => SameSize (Node2 rk1 rv1 (Node2 k1 v1 l' rl) (Node2 rk2 rv2 rm rr))
  delete k lk ku (Node2 k1 v1 l r) | EQ kk1 with (append l r)
    | ItFits lr          = TooSmall lr
    | TooBig k' v' l' r' = SameSize (Node2 k' v' l' r')
  delete k lk ku (Node2 k1 v1 l r) | GT k1k with (delete k (LTLift k1k) ku r)
    | SameSize r' = SameSize (Node2 k1 v1 l r')
    | TooSmall r' = case l of
        Node2 lk lv ll lr              => TooSmall (Node3 lk lv k1 v1 ll lr r')
        Node3 lk1 lv1 lk2 lv2 ll lm lr => SameSize (Node2 lk2 lv2 (Node2 lk1 lv1 ll lm) (Node2 k1 v1 lr r'))
delete k lk ku (Node3 k1 v1 k2 v2 l m r) with (the (Trichotomy ltR k k1) (trichotomy k k1))
  delete k lk ku (Node3 k1 v1 k2 v2 l m r) | LT kk1 with (delete k lk (LTLift kk1) l)
    | SameSize l' = SameSize (Node3 k1 v1 k2 v2 l' m r)
    | TooSmall l' = case m of
        Node2 mk mv ml mr              => SameSize (Node2 k2 v2 (Node3 k1 v1 mk mv l' ml mr) r)
        Node3 mk1 mv1 mk2 mv2 ml mm mr => SameSize (Node3 mk1 mv1 k2 v2 (Node2 k1 v1 l' ml) (Node2 mk2 mv2 mm mr) r)
  delete k lk ku (Node3 k1 v1 k2 v2 l m r) | EQ kk1 with (append l m)
    | ItFits lm          = SameSize (Node2 k2 v2 lm r)
    | TooBig k' v' l' m' = SameSize (Node3 k' v' k2 v2 l' m' r)
  delete k lk ku (Node3 k1 v1 k2 v2 l m r) | GT k1k with (the (Trichotomy ltR k k2) (trichotomy k k2))
    delete k lk ku (Node3 k1 v1 k2 v2 l m r) | GT k1k | LT kk2 with (delete k (LTLift k1k) (LTLift kk2) m)
      | SameSize m' = SameSize (Node3 k1 v1 k2 v2 l m' r)
      | TooSmall m' = case l of
          Node2 lk lv ll lr              => SameSize (Node2 k2 v2 (Node3 lk lv k1 v1 ll lr m') r)
          Node3 lk1 lv1 lk2 lv2 ll lm lr => SameSize (Node3 lk2 lv2 k2 v2 (Node2 lk1 lv1 ll lm) (Node2 k1 v1 lr m') r)
    delete k lk ku (Node3 k1 v1 k2 v2 l m r) | GT k1k | EQ kk2 with (append m r)
      | ItFits mr          = SameSize (Node2 k1 v1 l mr)
      | TooBig k' v' m' r' = SameSize (Node3 k1 v1 k' v' l m' r')
    delete k lk ku (Node3 k1 v1 k2 v2 l m r) | GT k1k | GT k2k with (delete k (LTLift k2k) ku r)
      | SameSize r' = SameSize (Node3 k1 v1 k2 v2 l m r')
      | TooSmall r' = case m of
          Node2 mk mv ml mr              => SameSize (Node2 k1 v1 l (Node3 mk mv k2 v2 ml mr r'))
          Node3 mk1 mv1 mk2 mv2 ml mm mr => SameSize (Node3 k1 v1 mk2 mv2 l (Node2 mk1 mv1 ml mm) (Node2 k2 v2 mr r'))
