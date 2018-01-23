module TMustache.Valuation

import Data.So
import TMustache.Relation.Order
import TMustache.Relation.Order.Instances
import TMustache.Data.Map as Map

%default total
%access public export

data MkType =
    MkString
  | MkBool

mkType : MkType -> Type
mkType MkString = String
mkType MkBool   = Bool

mkTypeM : Maybe MkType -> Type
mkTypeM = maybe Void mkType

infix 10 :=
data Assignment : String -> Map StringLT MkType -> Type where
  (:=) : (k : String) -> Valuation.mkTypeM (lookup k m) -> Assignment k m

infixr 7 ::
data Valuation : Map StringLT MkType -> Type where
  Nil  : Valuation map
  (::) : Assignment k m -> Valuation (Map.delete k m) -> Valuation m

-- Notice that in theory it should be possible to write a function of type:
-- value : (tag : String) -> Valuation s -> So (lookup tag s) -> Assignment tag s

value : (tag : String) -> Valuation m -> Maybe (Assignment tag m)
value tag []               = Nothing
value tag ((k := v) :: vs) = case compareBy StringLT tag k of
  EQ eq => Just (tag := rewrite eq in v)
  _     => believe_me (value tag vs)


private
test : Valuation (Map.fromList [("x", MkString), ("y", MkBool)])
test = "y" := True
    :: "x" := "This is x!"
    :: []

