module TMustache.TMustache

import TMustache.Data.Set
import TMustache.Relation.Order.Instances

import TMustache.Valuation

%default total
%access public export

data Mustache : Set StringLT -> Type where
  Nothing : Mustache empty
  PHolder : (tag : String) -> Mustache s -> Mustache (insert tag s)
  Content : String -> Mustache s -> Mustache s

ExMustache : Type
ExMustache = (s : Set StringLT ** Mustache s)

semantics : (m : ExMustache) -> Valuation (fst m) -> String
semantics (_ ** m) set = unsafeSemantics m where

  -- can't be bothered to maintain the invariant that the template
  -- and the valuation range over the same set. Happy with knowing
  -- that this is the case when calling `semantics` and that safety
  -- holds as a meta-result

  unsafeValue : String -> String
  unsafeValue s = case value s set of
    Nothing       => "IMPOSSIBLE"
    Just (s := v) => v

  unsafeSemantics : Mustache s -> String
  unsafeSemantics Nothing         = ""
  unsafeSemantics (Content str m) = str <+> unsafeSemantics m
  unsafeSemantics (PHolder tag m) = unsafeValue tag <+> unsafeSemantics m
