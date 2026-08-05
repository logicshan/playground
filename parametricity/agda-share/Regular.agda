
module Regular where

-- This module has two implementations of the language of
-- regular types and their terms, as found in McBride's
-- The Derivative of a Regular Type is its Type of One-Hole
-- Contexts:
--
--  http://www.cs.nott.ac.uk/~ctm/diff.pdf
--
-- The first uses a minimal set of constructors, and shows
-- that you can implement weakening and substitution by
-- induction. The second uses extra constructors for
-- substitution and weakening as suggested in the paper.
-- Both implementations use De Bruijn indices instead of
-- names.

open import Data.Fin hiding (_+_ ; _-_)
open import Data.Nat hiding (_+_ ; _<_)
open import Data.Unit
open import Data.Empty
open import Data.Function

open import Relation.Nullary
open import Relation.Binary.Core

infixl 60 _,_
data Env' (T : ℕ → Set) : (n : ℕ) → Set where
  ε   : Env' T zero
  _,_ : ∀{n} → (Γ : Env' T n) → (S : T n) → Env' T (suc n)

_-_ : (n : ℕ) → Fin n → ℕ
zero  - ()
suc m - zero  = m
suc m - suc n = m - n

infixl 40 _!_
_!_ : ∀{n T} → Env' T n → (f : Fin n) → T (n - f)
ε     ! ()
_ , x ! zero  = x
e , _ ! suc n = e ! n

slice : ∀{n T} → Env' T n → (f : Fin n) → Env' T (n - f)
slice ε       ()
slice (l , _) zero    = l
slice (l , _) (suc n) = slice l n

module Inductive where

  p≤p : ∀{m n} → Data.Nat._<_ (suc m) (suc n) → Data.Nat._<_ m n
  p≤p (s≤s m≤n) = m≤n

  p≤p' : ∀{n} {i j : Fin n} → Data.Fin._≤_ (suc i) (suc j) → Data.Fin._≤_ i j
  p≤p' (s≤s i≤j) = i≤j

  p≡p : ∀{n} {i j : Fin n} → _≡_ {Fin (suc n)} (suc i) (suc j) → i ≡ j
  p≡p refl = refl

  s≡s : ∀{n} {i j : Fin n} → i ≡ j → _≡_ {Fin (suc n)} (suc i) (suc j)
  s≡s refl = refl

  cmp : ∀{n} → Trichotomous _≡_ (_<_ {n})
  cmp zero    zero    = tri≈ (λ())     refl  (λ())
  cmp zero    (suc j) = tri< (s≤s z≤n) (λ()) (λ())
  cmp (suc i) zero    = tri> (λ())     (λ()) (s≤s z≤n)
  cmp (suc i) (suc j) with cmp i j
  ... | tri<  lt ¬eq ¬gt = tri< (s≤s lt)    (¬eq ∘ p≡p) (¬gt ∘ p≤p)
  ... | tri> ¬lt ¬eq  gt = tri> (¬lt ∘ p≤p) (¬eq ∘ p≡p) (s≤s gt)
  ... | tri≈ ¬lt  eq ¬gt = tri≈ (¬lt ∘ p≤p) (s≡s eq)    (¬gt ∘ p≤p)

  lower : ∀{n} i {j : Fin (suc n)} → i < j → Fin n
  lower {suc n}    zero {j}      i<j = zero
  lower {zero}     zero {zero}   ()
  lower {zero}     zero {suc ()} i<j
  lower {zero}     (suc ())      i<j
  lower {suc n}    (suc i) {zero} ()
  lower {suc n}    (suc i) {suc j} (s≤s i<j) = suc (lower i i<j)

  pre : ∀{n i} (j : Fin (suc n)) → flip₁ _<_ j i → Fin n
  pre         zero     ()
  pre {zero}  (suc ()) j>i
  pre {suc n} (suc j)  j>i = j


  infix 30 μ_
  infix 40 _+_
  infix 50 _×_
  data Reg : ℕ → Set where
    ref : ∀{n} → Fin n → Reg n
    `0` : ∀{n} → Reg n
    `1` : ∀{n} → Reg n
    _+_ : ∀{n} → Reg n → Reg n → Reg n
    _×_ : ∀{n} → Reg n → Reg n → Reg n
    μ_  : ∀{n} → Reg (suc n) → Reg n

  -- Rebuilds a term to allow for an extra environmental
  -- binding. For 'bind i F', refs <i are assumed to be
  -- bound by a μ, and are left the same (just injected
  -- into a higher rank finite set), while those ≥i are
  -- incremented, to refer to one space later in the
  -- environment. Of course, traversing past a μ increments
  -- i for the subterm
  bump : ∀{n} → Fin (suc n) → Reg n → Reg (suc n)
  bump i (ref j) with cmp (inject₁ j) i
  ... | tri< j<i _   _ = ref (inject₁ j)
  ... | _              = ref (suc j)
  bump i `0`     = `0`
  bump i `1`     = `1`
  bump i (S + T) = bump i S + bump i T
  bump i (S × T) = bump i S × bump i T
  bump i (μ T)   = μ bump (suc i) T

  -- Rebuilds a term to be valid in a context with an
  -- additional, irrelevant binding.
  infix 70 ↑_
  ↑_ : ∀{n} → Reg n → Reg (suc n)
  ↑_ = bump zero

  -- Rebuilds a term, substituting a term in for a certain
  -- index, and decrementing indices that refer into the
  -- environment, as if the substituted expression had been
  -- pulled out of it.
  replace : ∀{n} → (Fin (suc n)) → Reg (suc n) → Reg n → Reg n
  replace i (ref j) S with cmp j i
  ... | tri< j<i _ _ = ref (lower j j<i)
  ... | tri≈ _ j≡i _ = S
  ... | tri> _ _ j>i = ref (pre j j>i)
  replace i `0`     S = `0`
  replace i `1`     S = `1`
  replace i (T + U) S = replace i T S + replace i U S
  replace i (T × U) S = replace i T S × replace i U S
  replace i (μ T)   S = μ replace (suc i) T (↑ S)

  -- Uses the above procedure to substitute for the least
  -- position in the environment
  _/_ : ∀{n} → Reg (suc n) → Reg n → Reg n
  F / S = replace zero F S

  Env : ℕ → Set
  Env = Env' Reg

  infix 45 _⟦_⟧
  data _⟦_⟧ : ∀{n} → Env n → Reg n → Set where
    ⟨⟩    : ∀{n} {Γ : Env n} → Γ ⟦ `1` ⟧
    ⟨_,_⟩ : ∀{n} {Γ : Env n} {S T : Reg n}
          → (s : Γ ⟦ S ⟧) (t : Γ ⟦ T ⟧) → Γ ⟦ S × T ⟧
    inl   : ∀{n} {Γ : Env n} {S T : Reg n}
          → (s : Γ ⟦ S ⟧) → Γ ⟦ S + T ⟧
    inr   : ∀{n} {Γ : Env n} {S T : Reg n}
          → (t : Γ ⟦ T ⟧) → Γ ⟦ S + T ⟧
    con   : ∀{n} {Γ : Env n} {F : Reg (suc n)}
          → (t : Γ ⟦ F / μ F ⟧) → Γ ⟦ μ F ⟧
    sub   : ∀{n} {Γ : Env n} {F : Reg (suc n)} {S : Reg n}
          → (t : Γ , S ⟦ F ⟧) → Γ ⟦ F / S ⟧
    ix    : ∀{n} {Γ : Env n} {i : Fin n}
          → (t : slice Γ i ⟦ Γ ! i ⟧) → Γ ⟦ ref i ⟧
    k     : ∀{n} {Γ : Env n} {S : Reg n} {T : Reg n}
          → (t : Γ ⟦ T ⟧) → Γ , S ⟦ ↑ T ⟧

  bool : ∀{n} → Reg n
  bool = `1` + `1`

  nat : ∀{n} → Reg n
  nat = μ `1` + ref zero

  list : ∀{n} → Reg n → Reg n
  list T = μ `1` + ↑ T × ref zero

  ftree : ∀{n} → Reg n
  ftree = μ list (ref zero)

  true : ∀{n} {Γ : Env n} → Γ ⟦ bool ⟧
  true = inl ⟨⟩

  false : ∀{n} {Γ : Env n} → Γ ⟦ bool ⟧
  false = inr ⟨⟩

{- These have problems with unsovled metavariables that I don't feel
   like fixing. This version requires significantly more annotation
   it seems
  z : ∀{n} {Γ : Env n} → Γ ⟦ nat ⟧
  z {n} = con (sub (inl ⟨⟩))

  s : ∀{n} {Γ : Env n} → Γ ⟦ nat ⟧ → Γ ⟦ nat ⟧
  s n = con (sub (inr (ix n)))

  btree : ∀{n} → Reg n
  btree = μ `1` + ref zero × ref zero

  bleaf : ∀{n} {Γ : Env n} → Γ ⟦ btree ⟧
  bleaf = con (sub (inl ⟨⟩))

  bnode : ∀{n} {Γ : Env n} → Γ ⟦ btree ⟧ → Γ ⟦ btree ⟧ → Γ ⟦ btree ⟧
  bnode l r = con (sub (inr ⟨ ix l , ix r ⟩))

  nil : ∀{n} {Γ : Env n} {T : Reg n} → Γ ⟦ list T ⟧
  nil = con (sub (inl ⟨⟩))

  _::_ : ∀{n} {Γ : Env n} {T : Reg n} → Γ ⟦ T ⟧ → Γ ⟦ list T ⟧ → Γ ⟦ list T ⟧
  x :: xs = con (sub (inr ⟨ k x , ix xs ⟩))
-}

module Axiomatic where
  infix 30 μ_
  infix 40 _+_
  infix 50 _×_
  infix 70 ↑_

  data Reg : ℕ → Set where
    ref  : ∀{n} → Fin n → Reg n
    `0`  : ∀{n} → Reg n
    `1`  : ∀{n} → Reg n
    _+_  : ∀{n} → Reg n → Reg n → Reg n
    _×_  : ∀{n} → Reg n → Reg n → Reg n
    μ_   : ∀{n} → Reg (suc n) → Reg n
    _/_  : ∀{n} (F : Reg (suc n)) (S : Reg n) → Reg n
    ↑_   : ∀{n} (T : Reg n) → Reg (suc n)

  Env : ℕ → Set
  Env = Env' Reg

  bool : ∀{n} → Reg n
  bool = `1` + `1`

  nat : ∀{n} → Reg n
  nat = μ `1` + ref zero

  list : ∀{n} → Reg n → Reg n
  list T = μ `1` + ↑ T × ref zero

  ftree : ∀{n} → Reg n
  ftree = μ list (ref zero)

  infix 45 _⟦_⟧
  data _⟦_⟧ : ∀{n} → Env n → Reg n → Set where
    ⟨⟩    : ∀{n} {Γ : Env n} → Γ ⟦ `1` ⟧
    ⟨_,_⟩ : ∀{n} {Γ : Env n} {S T : Reg n}
          → (s : Γ ⟦ S ⟧) (t : Γ ⟦ T ⟧) → Γ ⟦ S × T ⟧
    inl   : ∀{n} {Γ : Env n} {S T : Reg n}
          → (s : Γ ⟦ S ⟧) → Γ ⟦ S + T ⟧
    inr   : ∀{n} {Γ : Env n} {S T : Reg n}
          → (t : Γ ⟦ T ⟧) → Γ ⟦ S + T ⟧
    con   : ∀{n} {Γ : Env n} {F : Reg (suc n)}
          → (t : Γ ⟦ F / μ F ⟧) → Γ ⟦ μ F ⟧
    sub   : ∀{n} {Γ : Env n} {F : Reg (suc n)} {S : Reg n}
          → (t : Γ , S ⟦ F ⟧) → Γ ⟦ F / S ⟧
    ix    : ∀{n} {Γ : Env n} {i : Fin n}
          → (t : slice Γ i ⟦ Γ ! i ⟧) → Γ ⟦ ref i ⟧
    k     : ∀{n} {Γ : Env n} {S : Reg n} {T : Reg n}
          → (t : Γ ⟦ T ⟧) → Γ , S ⟦ ↑ T ⟧

  true : ∀{n} {Γ : Env n} → Γ ⟦ bool ⟧
  true = inl ⟨⟩

  false : ∀{n} {Γ : Env n} → Γ ⟦ bool ⟧
  false = inr ⟨⟩

  z : ∀{n} {Γ : Env n} → Γ ⟦ nat ⟧
  z = con (sub (inl ⟨⟩))

  s : ∀{n} {Γ : Env n} → Γ ⟦ nat ⟧ → Γ ⟦ nat ⟧
  s n = con (sub (inr (ix n)))

  btree : ∀{n} → Reg n
  btree = μ `1` + ref zero × ref zero

  bleaf : ∀{n} {Γ : Env n} → Γ ⟦ btree ⟧
  bleaf = con (sub (inl ⟨⟩))

  bnode : ∀{n} {Γ : Env n} → Γ ⟦ btree ⟧ → Γ ⟦ btree ⟧ → Γ ⟦ btree ⟧
  bnode l r = con (sub (inr ⟨ ix l , ix r ⟩))

  nil : ∀{n} {Γ : Env n} {T : Reg n} → Γ ⟦ list T ⟧
  nil = con (sub (inl ⟨⟩))

  _::_ : ∀{n} {Γ : Env n} {T : Reg n} → Γ ⟦ T ⟧ → Γ ⟦ list T ⟧ → Γ ⟦ list T ⟧
  x :: xs = con (sub (inr ⟨ k x , ix xs ⟩))
