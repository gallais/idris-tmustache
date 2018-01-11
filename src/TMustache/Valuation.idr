module TMustache.Valuation

import Data.So
import TMustache.Relation.Order
import TMustache.Relation.Order.Instances
import TMustache.Data.Set as Set

%default total
%access public export

infix 10 :=
data Assignment : String -> Type where
  (:=) : (s, v : String) -> Assignment s

infixr 7 ::
data Valuation : Set StringLT -> Type where
  Nil  : Valuation Set.empty
  (::) : Assignment s -> Valuation (Set.delete s set) -> Valuation set

-- Notice that in theory it should be possible to write a function of type:
-- value : (tag : String) -> Valuation s -> So (elem tag s) -> Assignment tag

value : (tag : String) -> Valuation s -> Maybe (Assignment tag)
value tag []                = Nothing
value tag ((nm := v) :: vs) = case compareBy StringLT tag nm of
  EQ _ => Just (tag := v)
  _    => value tag vs

private
test : Valuation (Set.fromList ["x", "y"])
test = "y" := "This is y!"
    :: "x" := "This is x!"
    :: []


