module Zip where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC suc #-}

data _×_ (a b : Set) : Set where
  _,_ : a -> b -> a × b

infixr 40 _::_ _::₁_ _<|_ _,,_

data [_] (a : Set) : Set where
  [] : [ a ]
  _::_ : a -> [ a ] -> [ a ]

data [_]₁ (a : Set1) : Set1 where
  []₁   : [ a ]₁
  _::₁_ : a -> [ a ]₁ -> [ a ]₁

data TVec : Nat -> Set1 where
  <> : TVec zero
  _<|_ : {n : Nat} -> Set -> TVec n -> TVec (suc n)

data Tuple : {n : Nat} -> TVec n -> Set1 where
  zt : Tuple <>
  _,,_ : {a : Set}{n : Nat}{ts : TVec n} -> a -> Tuple ts -> Tuple (a <| ts)

zip : forall {a b} -> [ a ] -> [ b ] -> [ a × b ]
zip [] _ = []
zip _ [] = []
zip (a :: as) (b :: bs) = (a , b) :: zip as bs

lists : forall {n} -> TVec n -> TVec n
lists <> = <>
lists (t <| ts) = [ t ] <| lists ts

zipT : {n : Nat}{ts : TVec n} -> Tuple (lists ts) -> [ Tuple ts ]₁
zipT {zero}     {<>}      zt        = []₁
zipT {suc zero} {t <| <>} (l ,, zt) = mapTup l
 where
 mapTup : [ t ] -> [ Tuple (t <| <>) ]₁
 mapTup [] = []₁
 mapTup (a :: as) = (a ,, zt) ::₁ mapTup as

zipT {suc n}    {t <| ts} (l ,, tu) = zipTup l (zipT tu)
 where
 zipTup : [ t ] -> [ Tuple ts ]₁ -> [ Tuple (t <| ts) ]₁
 zipTup [] _   = []₁
 zipTup _  []₁ = []₁
 zipTup (a :: as) (t ::₁ ts) = (a ,, t) ::₁ zipTup as ts

foo = zipT ((zero :: zero :: zero :: []) ,, (zero :: zero :: []) ,, zt)

fun : forall {n} -> TVec n -> Set -> Set
fun <> r = r
fun (t <| ts) r = t -> fun ts r

uncurryT : {n : Nat}{ts : TVec n}{r : Set} -> fun ts r -> Tuple ts -> r
uncurryT {zero}  {<>}      {r} v zt = v
uncurryT {suc n} {t <| ts} {r} f (a ,, as) = uncurryT (f a) as

curryT : {n : Nat}{ts : TVec n}{r : Set} -> (Tuple ts -> r) -> fun ts r
curryT {zero}  {<>}      {r} f = f zt
curryT {suc n} {t <| ts} {r} f = \v -> curryT (\t -> f (v ,, t))

zipWithT : {n : Nat}{ts : TVec n}{r : Set} -> fun ts r -> fun (lists ts) [ r ]
zipWithT {n} {ts} {r} f
  = curryT {n} {lists ts} {[ r ]} (\t -> map₁ (uncurryT {n} {ts} {r} f) (zipT t))
 where
 map₁ : forall {t r} -> (t -> r) -> [ t ]₁ -> [ r ]
 map₁ _ []₁ = []
 map₁ f (a ::₁ as) = f a :: map₁ f as

infixl 40 _+_
_+_ : Nat -> Nat -> Nat
zero    + n = n
(suc m) + n = suc (m + n)

l1 = zero :: zero :: zero :: []
l2 = suc (suc zero) :: suc zero :: zero :: []
l3 = zero :: suc zero :: suc (suc zero) :: suc (suc (suc zero)) :: []

bar = zipWithT {_} {Nat <| Nat <| Nat <| <>} (\a b c -> a + b + c) l1 l2 l3
