module TMustache.Valuation

import Data.So
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

private
test : Valuation (Set.fromList ["x", "y"])
test = "y" := "This is y!"
    :: "x" := "This is x!"
    :: []


