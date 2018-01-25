module Main

import TMustache.Relation.Order.Instances
import TMustache.Data.Map
import TMustache.Data.Star
import TMustache.Data.DiffExists
import TMustache.TMustache
import TMustache.Valuation
import TMustache.Provider
import TMustache.Parser

import Common
import Prelude.Providers

%default total

%language TypeProviders
%provide (raw : String) with rawFile "Hello.mst"

must : ExMustache
must = fromJust (parseMustache raw)

main : IO ()
main = do
  putStrLn $ semantics must $ "name" := "World" :: []
--  putStrLn $ semantics must $ "world" := "Name" :: Nil -- rejected
