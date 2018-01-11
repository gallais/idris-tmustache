module Hello

import TMustache.Relation.Order.Instances
import TMustache.Data.Set
import TMustache.TMustache
import TMustache.Valuation
import TMustache.Provider

import Prelude.Providers

%language TypeProviders
%provide (must : ExMustache) with tmustache "Hello.mst"

%default total

index : Set StringLT
index = DPair.fst must

valuation : Valuation Hello.index
valuation = "name" := "World" :: []

main : IO ()
main = do
  putStrLn $ semantics must ?a -- ("name" := "World" :: [])
--  putStrLn $ semantics must $ "world" := "Name" :: []
