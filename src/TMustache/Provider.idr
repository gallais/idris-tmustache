module TMustache.Provider

import TMustache.Data.Set
import TMustache.Relation.Order.Instances
import TMustache.TMustache
import TMustache.Parser

import TParsec.Running

import Prelude.Providers
%language TypeProviders

%default total
%access public export

tmustache : String -> IO (Provider ExMustache)
tmustache fp = do
  Right raw <- readFile fp | Left err => pure (Error (show err))
  let Just m = parseMustache raw | Nothing => pure (Error "Invalid Mustache File")
  pure $ Provide m
