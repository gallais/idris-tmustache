module Main

import TMustache.Relation.Order.Instances
import TMustache.Data.Set
import TMustache.TMustache
import TMustache.Valuation
import TMustache.Provider
import TMustache.Parser

import Prelude.Providers

%default total

%language TypeProviders
-- %provide (must : ExMustache) with tmustache "Time.mst"

main : IO ()
main = do
{-
  putStrLn $ semantics must
    $ "hours"   := "05"
   :: "minutes" := "37"
   :: "am"      := True
   :: "pm"      := False
   :: []                  -}
  Right txt <- readFile "Time.mst" | Left => putStrLn "file error"
  case parseMustache txt of
    Just _  => putStrLn "success"
    Nothing => putStrLn "parse error"
