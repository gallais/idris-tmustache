module TMustache.TMustache

import TMustache.Data.DiffExists
import TMustache.Data.Star
import TMustache.Data.Map as Map
import TMustache.Relation.Order.Instances

import TMustache.Valuation

%default total
%access public export

mutual

  data MustacheBlock : Map StringLT MkType -> Map StringLT MkType -> Type where
    -- placeholder to be replaced by content
    PHolder : (tag : String) -> MustacheBlock s (override tag MkString s)
    -- block conditionned by the boolean value associated to PCond
    PCond   : (tag : String) -> Mustache (override tag MkBool s) t -> MustacheBlock s t
    -- simple string content
    Content : String -> MustacheBlock s s

  Mustache : Map StringLT MkType -> Map StringLT MkType -> Type
  Mustache = Star MustacheBlock

ExMustache : Type
ExMustache = DiffExists (Map StringLT MkType) Mustache

semantics : (m : ExMustache) -> Valuation (index m Map.empty) -> String
semantics (MkDiffExists dmp must) vs = unsafeSems (must Map.empty) where

  mp : Map StringLT MkType
  mp = dmp Map.empty

  -- can't be bothered to maintain the invariant that the template
  -- and the valuation range over the same set. Happy with knowing
  -- that this is the case when calling `semantics` and that safety
  -- holds as a meta-result

  unsafeVal : (tag : String) -> Lazy String -> String
  unsafeVal tag str with (Map.lookup tag mp, value tag vs)
    | (Nothing, _)             = "IMPOSSIBLE"
    | (_, Nothing)             = "IMPOSSIBLE"
    | (Just mk, Just (_ := v)) = case mk of
      MkString => believe_me v
      MkBool   => if believe_me v then str else ""

  mutual

    unsafeSems : Mustache s t -> String
    unsafeSems [] = ""
    unsafeSems (t :: ts) = unsafeSem t <+> unsafeSems ts

    unsafeSem : MustacheBlock s t -> String
    unsafeSem (Content str) = str
    unsafeSem (PCond tag m) = unsafeVal tag (unsafeSems m)
    unsafeSem (PHolder tag) = unsafeVal tag ""
