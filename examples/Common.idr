module Common

%default total
%access public export

fromJust : (m : Maybe a) -> {auto pr : isJust m = True} -> a
fromJust Nothing {pr} = absurd pr
fromJust (Just a) = a

