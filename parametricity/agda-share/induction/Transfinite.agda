
module Transfinite where

data ⊥ : Set where

record ⊤ : Set where

data Σ (a : Set) (P : a → Set) : Set where
  _,_ : (x : a) (w : P x) → Σ a P

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

data Ordinal : Set where
  zero : Ordinal
  _+1  : Ordinal → Ordinal
  lim  : (ℕ → Ordinal) → Ordinal

from-ℕ : ℕ → Ordinal
from-ℕ 0       = zero
from-ℕ (suc n) = from-ℕ n +1

ω : Ordinal
ω = lim from-ℕ

ω∙2 : Ordinal
ω∙2 = lim g
 where
 g : ℕ → Ordinal
 g 0       = ω
 g (suc n) = g n +1

_+_ : Ordinal → Ordinal → Ordinal
o + zero  = o
o + o' +1 = (o + o') +1
o + lim f = lim (λ n → o + f n)

_∙_ : Ordinal → Ordinal → Ordinal
o ∙ zero  = zero
o ∙ o' +1 = (o ∙ o') + o
o ∙ lim f = lim (λ n → o ∙ f n)

ω² : Ordinal
ω² = lim (λ n → ω ∙ from-ℕ n)

_^_ : Ordinal → Ordinal → Ordinal
o ^ zero  = zero +1
o ^ o' +1 = (o ^ o') ∙ o
o ^ lim f = lim (λ n → o ^ f n)

_^^_ : Ordinal → ℕ → Ordinal
o ^^ 0     = zero +1
o ^^ 1     = o
o ^^ suc n = o ^ (o ^^ n)

ε₀ : Ordinal
ε₀ = lim (_^^_ ω)

_≤_ : Ordinal → Ordinal → Set
zero    ≤ _     = ⊤
o +1    ≤ zero  = ⊥
o +1    ≤ p +1  = o ≤ p
o +1    ≤ lim g = Σ ℕ λ n → o +1 ≤ g n
(lim f) ≤ o     = ∀ n → f n ≤ o

_<_ : Ordinal → Ordinal → Set
o < p = o +1 ≤ p

trans-≤ : ∀ i j k → i ≤ j → j ≤ k → i ≤ k
trans-≤ zero    j       k       i≤j j≤k         = _
trans-≤ (i +1)  zero    k       ()  j≤k
trans-≤ (i +1)  (j +1)  zero    i≤j ()
trans-≤ (i +1)  (j +1)  (k +1)  i≤j j≤k         = trans-≤ i j k i≤j j≤k
trans-≤ (i +1)  (j +1)  (lim h) i≤j (n , sj≤hn) = (n , trans-≤ (i +1) (j +1) (h n) i≤j sj≤hn)
trans-≤ (i +1)  (lim g) k       (n , si≤gn) j≤k = trans-≤ (i +1) (g n) k si≤gn (j≤k n)
trans-≤ (lim f) j       k       i≤j         j≤k = λ n → trans-≤ (f n) j k (i≤j n) j≤k

transfinite : ∀{P : Ordinal → Set} → (∀ o → (∀ o' → o' < o → P o') → P o) → (o : Ordinal) → P o
transfinite {P} Φ o = Φ o (λ o' o'<o → aux o o' o'<o)
 where
 aux : ∀ o o' → o' < o → P o'
 aux zero    o'    ()
 aux (o +1) zero    o'<o = Φ zero (λ _ ())
 aux (o +1) (o' +1) o'<o = Φ (o' +1) (λ o'' o''<o' → aux o o'' 
                                        (trans-≤ (o'' +1) (o' +1) o o''<o' o'<o))
 aux (o +1) (lim g) o'<o = Φ (lim g) f
   where
   f : ∀ o'' → o'' < lim g → P o''
   f o'' (n , o''<gn) = aux o o'' (trans-≤ (o'' +1) (g n) o o''<gn (o'<o n))
 aux (lim f) o' (n , o'<fn) = aux (f n) o' o'<fn







