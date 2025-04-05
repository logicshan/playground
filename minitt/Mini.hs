{-# LANGUAGE UnicodeSyntax #-}

module Mini where

type Name = String

data G a = Success a | Fail Name

instance Functor G where
  fmap f (Success x) = Success (f x)
  fmap _ (Fail s) = Fail s

instance Applicative G where
  pure = Success
  (Success f) <*> (Success x) = Success (f x)
  (Fail s) <*> _  = Fail s
  _ <*> (Fail s) = Fail s

instance Monad G where
  (Success x) >>= k = k x
  Fail s      >>= k = Fail s

instance MonadFail G where
    fail ∷ String → G a
    fail s = Fail s

