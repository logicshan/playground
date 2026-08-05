
-- This implements a view of functions with finite domains
-- such that matching against the view expands the function
-- to look like vector indexing. I could have sworn I've seen
-- this in a paper on Epigram, but I have been unable to find
-- such a paper in my folder containing them.
module FunView where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

infixl 50 _+_
_+_ : ℕ → ℕ → ℕ
0     + n = n
suc m + n = suc (m + n)

data Fin : ℕ → Set where
  zero : ∀{n} → Fin (1 + n)
  suc  : ∀{n} → Fin n → Fin (1 + n)

data Vec (A : Set) : ℕ → Set where
  []   : Vec A 0
  _::_ : ∀{n} → (x : A) (xs : Vec A n) → Vec A (1 + n)

infix 40 _!_
_!_ : ∀{A n} → Vec A n → Fin n → A
[]        ! ()
(_ :: xs) ! suc n = xs ! n
(x :: _)  ! zero  = x

tabulate : ∀{A n} → (Fin n → A) → Vec A n
tabulate {n = 0}     _ = []
tabulate {n = suc n} f = f zero :: tabulate {n = n} (λ i → f (suc i))

data View {A n} : (Fin n → A) → Set where
  vlam : (v : Vec A n) → View (λ i → v ! i)

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

subst : ∀{A x y} (P : A → Set) → x ≡ y → P x → P y
subst _ refl Px = Px

postulate
  ext : ∀{A B : Set} {f g : A → B} → (∀ x → f x ≡ g x) → f ≡ g

lemma : ∀{A} n (f : Fin n → A) → ∀ i → tabulate f ! i ≡ f i
lemma {A} zero    f ()
lemma {A} (suc n) f zero    = refl
lemma {A} (suc n) f (suc i) = lemma n (λ i' → f (suc i')) i

tab-≡ : ∀{A n} {f : Fin n → A} → (λ i → tabulate f ! i) ≡ f
tab-≡ {A} {n} {f} = ext (lemma n f)


view-fun : ∀{n} {A : Set} → (f : Fin n → A) → View f
view-fun {n} {A} f = subst View tab-≡ (vlam (tabulate f))

f : Fin 10 → Fin 10
f i = i

zing : ∀{A n} (f : Fin n → A) → Vec A n
zing f with view-fun f
zing .(λ i →  v ! i) | vlam v = v
