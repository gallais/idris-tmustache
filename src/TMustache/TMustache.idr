module TMustache.TMustache

import TMustache.Data.DiffExists
import TMustache.Data.Star
import TMustache.Data.Map as Map
import TMustache.Relation.Order.Instances

import TMustache.Valuation

%default total
%access public export

Scope : Type
Scope = Map StringLT MkType

mutual

  data MustacheBlock : Scope -> Scope -> Type where
    -- placeholder to be replaced by content
    PHolder : (tag : String) -> MustacheBlock s (override tag MkString s)
    -- block conditionned by the boolean value associated to PCond
    IfCond  : (tag : String) -> Mustache (override tag MkBool s) t -> MustacheBlock s t
    -- foreach block conditioned by the list associated to PForEach
    ForEach : (tag : String) -> (t : Scope) -> Mustache Map.empty t -> MustacheBlock s (override tag (MkList t) s)
    -- simple string content
    Content : String -> MustacheBlock s s

  Mustache : Scope -> Scope -> Type
  Mustache = Star MustacheBlock

ExMustache : Type
ExMustache = DiffExists Scope Mustache

semantics : (m : ExMustache) -> Valuation (index m Map.empty) -> String
semantics (MkDiffExists dmp must) vs = unsafeSems vs (must Map.empty) where

  -- can't be bothered to maintain the invariant that the template
  -- and the valuation range over the same set. Happy with knowing
  -- that this is the case when calling `semantics` and that safety
  -- holds as a meta-result

  unsafeVal : (a : Type) -> (tag : String) -> Valuation t -> a
  unsafeVal a tag vs = case value tag vs of
    Nothing       => believe_me "IMPOSSIBLE"
    Just (_ := v) => believe_me v

  mutual

    unsafeSems : Valuation t -> Mustache s t -> String
    unsafeSems vs [] = ""
    unsafeSems vs (b :: bs) = unsafeSem (believe_me vs) b <+> unsafeSems (believe_me vs) bs

    unsafeSem : Valuation t -> MustacheBlock s t -> String
    unsafeSem vs (Content str)     = str
    unsafeSem vs (IfCond tag m)    = if (unsafeVal Bool tag vs) then unsafeSems (believe_me vs) m else ""
    unsafeSem vs (PHolder tag)     = unsafeVal String tag vs
    unsafeSem vs (ForEach tag t m) = concatMap (\ vs => unsafeSems (believe_me vs) m)
                                   $ unsafeVal (List (Valuation t)) tag vs
