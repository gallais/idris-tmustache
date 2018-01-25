module TMustache.Valuation

import TMustache.Relation.Order
import TMustache.Relation.Order.Instances
import TMustache.Data.Map as Map

%default total
%access public export

data MkType =
    MkString
  | MkBool
  | MkList (Map StringLT MkType)

mkTypeM : Maybe Type -> Type
mkTypeM = maybe Void (\ t => t)

mutual

  mkType : MkType -> Type
  mkType (MkList s) = List (Valuation s)
  mkType MkString   = String
  mkType MkBool     = Bool


  infix 10 :=
  data Assignment : String -> Map StringLT MkType -> Type where
    (:=) : (k : String) -> Valuation.mkTypeM (map Valuation.mkType $ lookup k m) -> Assignment k m

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
test : let m = Map.fromList [("x", MkString), ("y", MkBool)]
      in Valuation (Map.fromList [("e", MkString), ("xys", MkList m)])
test = "e"   := "This is e!"
    :: "xys" := [ ("y" := True :: "x" := "This is x!" :: [])
                , ("x" := "This is not x!" :: "y" := False :: [])
                ]
    :: []

