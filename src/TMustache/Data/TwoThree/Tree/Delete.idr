module TMustache.Data.TwoThree.Tree.Delete

import TMustache.Relation.Order

import TMustache.Data.TwoThree.Key
import TMustache.Data.TwoThree.Tree.Type
import TMustache.Data.TwoThree.Tree.Base

%default total
%access public export

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
