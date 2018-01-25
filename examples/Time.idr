module Main

import TMustache.Relation.Order.Instances
import TMustache.TMustache
import TMustache.Data.Map
import TMustache.Data.Star
import TMustache.Data.DiffExists
import TMustache.Valuation
import TMustache.Provider
import TMustache.Parser

import Common
import Prelude.Providers

%default total

%language TypeProviders
%provide (raw : String) with rawFile "Time.mst"

must : ExMustache
must = fromJust (parseMustache raw)

main : IO ()
main = do
  putStrLn $ semantics must
    $ "hours"   := "05"
   :: "minutes" := "37"
   :: "am"      := True
   :: "pm"      := False
   :: []
