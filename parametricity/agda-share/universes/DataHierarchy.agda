
module DataHierarchy where

open import Meta

data Descr : Set₁ where
   done : Descr
   ind  : Descr → Descr
   sig  : (S : Set) (D : S → Descr) → Descr

[_] : Descr → Set → Set
[ done ] X = X
[ ind D ] X = X × [ D ] X
[ sig S D ] X = Σ S (λ x → [ D x ] X)

data Fix (D : Descr) : Set where
  con : [ D ] (Fix D) → Fix D

module Build (U : Set) (Desc : Set) (T : U → Set) where
  mutual
    data Φ : Set where
      Π      : (s : Φ) (f : Θ s → Φ) → Φ
      desc u : Φ
      t      : U → Φ
      μ      : Δ → Φ

    Θ : Φ → Set
    Θ u = U
    Θ desc = Desc
    Θ (t s) = T s
    Θ (μ D) = Fix ⟦ D ⟧
    Θ (Π s f) = (x : Θ s) → Θ (f x)

    data Δ : Set where
      done : Δ
      ind  : Δ → Δ
      case : (n : ℕ) (c : Fin n → Δ) → Δ
      sig  : (s : Φ) (f : Θ s → Δ) → Δ

    ⟦_⟧ : Δ → Descr
    ⟦ done     ⟧  = done
    ⟦ ind  D   ⟧ = ind ⟦ D ⟧
    ⟦ case n c ⟧ = sig (Fin n) (λ i → ⟦ c i ⟧)
    ⟦ sig  s f ⟧ = sig (Θ s) (λ x → ⟦ f x ⟧)

open Build using (Φ ; Θ ; Δ ; Π)

mutual
  U' : ℕ → Set
  U' zero    = ⊥
  U' (suc n) = Φ (U' n) (Desc' n) (T' n) 

  T' : (n : ℕ) → U' n → Set
  T' zero    ()
  T' (suc n) s  = Θ (U' n) (Desc' n) (T' n) s

  Desc' : ℕ → Set
  Desc' zero    = ⊥
  Desc' (suc n) = Δ (U' n) (Desc' n) (T' n)

U : ℕ → Set
U n = U' (suc n)

T : (n : ℕ) → U n → Set
T n = T' (suc n)

Desc : (n : ℕ) → Set
Desc n = Desc' (suc n)

-- desc n : U (suc n)
desc : (n : ℕ) → U (suc n)
desc n = Build.desc

-- u n : U (suc n)
u : (n : ℕ) → U (suc n)
u n = Build.u

-- D : Desc n ⇒ μ D : U n
μ : {n : ℕ} → Desc n → U n
μ {n} D = Build.μ D

-- s : U n → t s : U (suc n)
t : {n : ℕ} → U n → U (suc n)
t s = Build.t s

