module TMustache.Data.LazyList

%default total
%access public export

data LazyList : Type -> Type where
  Nil  : LazyList a
  (::) : a -> Lazy (LazyList a) -> LazyList a


(++) : LazyList a -> LazyList a -> LazyList a
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

filter : (a -> Bool) -> LazyList a -> LazyList a
filter p []        = []
filter p (x :: xs) = if p x then x :: filter p xs else filter p xs

implementation Functor LazyList where

  map f []        = []
  map f (x :: xs) = f x :: map f xs

implementation Applicative LazyList where

  pure a = a :: []

  []        <*> xs = []
  (f :: fs) <*> xs = map f xs ++ (fs <*> xs)

implementation Alternative LazyList where

  empty = []

  xs <|> ys = xs ++ ys 

implementation Monad LazyList where

  []        >>= f = []
  (x :: xs) >>= f = f x ++ (xs >>= f)
