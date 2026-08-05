
module Countable where

open import Coinduction

open import Data.Empty
open import Data.Product

open import Relation.Binary.PropositionalEquality

data Coℕ : Set where
  zero : Coℕ
  suc  : ∞ Coℕ → Coℕ

ω : Coℕ
ω = suc (♯ ω)

infixl 60 _⊕_
_⊕_ : Coℕ → Coℕ → Coℕ
zero  ⊕ n = n
suc m ⊕ n = suc (♯ (♭ m ⊕ n))

infix 50 _≼_
data _≼_ : Coℕ → Coℕ → Set where
  z≼ : ∀{β}   → zero ≼ β
  s≼ : ∀{α β} → ∞ (♭ α ≼ ♭ β) → suc α ≼ suc β

α≼ω : ∀{α} → α ≼ ω
α≼ω {zero}  = z≼
α≼ω {suc α} = s≼ (♯ α≼ω)

data ∥_∥ : Coℕ → Set where
  zero : ∀{n}            → ∥ suc n ∥
  suc  : ∀{n} → ∥ ♭ n ∥ → ∥ suc n ∥

s≡s : ∀{α} {m n : ∥ ♭ α ∥} → m ≡ n → _≡_ {_} {∥ suc α ∥} (suc m) (suc n)
s≡s refl = refl

ℕ : Set
ℕ = ∥ ω ∥

{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

{-
↑ : ∀{α} → ∥ α ∥ → ∥ α ∥
↑ {zero}  ()
↑ {suc α} zero with inspect (♭ α)
... | it zero    _       = zero
... | it (suc _) suc_≡♭a = suc (subst ∥_∥ suc_≡♭a zero)
↑ {suc α} (suc m) = suc (↑ {♭ α} m)

+-aux : ∀ α {β} → ∥ α ∥ → ∥ β ∥ → ∥ β ∥
+-aux zero    ()      _
+-aux (suc α) zero    n = n
+-aux (suc α) (suc m) n = ↑ (+-aux (♭ α) m n)

infixl 60 _+_
_+_ : ∀{α} → ∥ α ∥ → ∥ α ∥ → ∥ α ∥
m + n = +-aux _ m n

*-aux : ∀ α β → ∥ α ∥ → ∥ β ∥ → ∥ β ∥
*-aux zero    _       ()      _
*-aux _       zero    _       ()
*-aux (suc α) (suc β) zero    _  = zero
*-aux (suc α) (suc β) (suc m) n  = n + *-aux (♭ α) (suc β) m n

infixl 65 _*_
_*_ : ∀{α} → ∥ α ∥ → ∥ α ∥ → ∥ α ∥
m * n = *-aux _ _ m n

mod : ∀{α} → ∥ ω ∥ → ∥ suc α ∥
mod n = +-aux ω n zero

mod' : ∀{α} → ∥ ω ∥ → ∥ suc α ∥
mod' {α} zero    = zero
mod' {α} (suc n) with inspect (♭ α)
... | it zero    _     = zero
... | it (suc β) sβ≡♭α = suc (subst ∥_∥ sβ≡♭α (mod' n))

lift₁ : ∀{α β} → ∥ α ∥ → ∥ α ⊕ β ∥
lift₁ {zero}  ()
lift₁ {suc α} n  = +-aux (suc α) n zero

lift₂ : ∀{α β} → α ≼ β → ∥ α ∥ → ∥ β ∥
lift₂ z≼     ()
lift₂ (s≼ p) zero    = zero
lift₂ (s≼ p) (suc n) = suc (lift₂ (♭ p) n)

m∘l≡id : ∀{α} → (n : ∥ suc α ∥) → mod' (lift₂ α≼ω n) ≡ n
m∘l≡id zero    = refl
m∘l≡id {α} (suc n) with inspect (♭ α)
... | it zero    eq    = {!!}
... | it (suc β) sβ≡♭α = s≡s {!!}

extend : ∀{α} {T : Set} → (∥ suc α ∥ → T) → ∥ ω ∥ → T
extend f n = f (mod n)

extend-covers : ∀{α T} {f : ∥ suc α ∥ → T} → ∀ m → ∃ λ n → f m ≡ extend f n
extend-covers m = {!!}

record _≅_ (T U : Set) : Set where
  field
    iso→ : T → U
    iso← : U → T

    id← : ∀ t → iso← (iso→ t) ≡ t
    id→ : ∀ u → iso→ (iso← u) ≡ u

open _≅_

Countable : Set → Set
Countable T = ∃ (λ α → ∥ α ∥ ≅ T)

Uncountable : Set → Set
Uncountable T = ∀(b : ℕ → T) → Σ T (λ t → ∀ n → t ≢ b n)

lemma₀ : ∀{T} → Uncountable T → ¬ Countable T
lemma₀ {T} uc c = {!!}
-- where
-- b : ℕ → T
-- b = extend (iso→ (π₂ c))
-}
