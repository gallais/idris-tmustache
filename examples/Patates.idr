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
%provide (raw : String) with rawFile "Patates.mst"

must : ExMustache
must = fromJust (parseMustache raw)

main : IO ()
main = do
  putStrLn $ semantics must
    $ "vers" := [ "jour" := "Lundi"    :: "aussi" := False :: []
                , "jour" := "Mardi"    :: "aussi" := False :: []
                , "jour" := "Mercredi" :: "aussi" := True :: []
                ]
    :: []
