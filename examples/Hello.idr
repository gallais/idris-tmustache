module Hello

import TMustache.Relation.Order.Instances
import TMustache.Data.Set
import TMustache.TMustache
import TMustache.Valuation
import TMustache.Provider

import Prelude.Providers

%default total

%language TypeProviders
%provide (must : ExMustache) with tmustache "Hello.mst"

main : IO ()
main = do
  putStrLn $ semantics must $ "name" := "World" :: []
--  putStrLn $ semantics must $ "world" := "Name" :: Nil -- rejected
