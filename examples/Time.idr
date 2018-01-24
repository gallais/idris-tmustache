module Time

import TMustache.Relation.Order.Instances
import TMustache.Data.Set
import TMustache.TMustache
import TMustache.Valuation
import TMustache.Provider

import Prelude.Providers

%default total

%language TypeProviders
%provide (must : ExMustache) with tmustache "Time.mst"

main : IO ()
main = do
  putStrLn $ semantics must
    $ "hours"   := "05"
   :: "minutes" := "37"
   :: "am"      := True
   :: "pm"      := False
   :: []                  
