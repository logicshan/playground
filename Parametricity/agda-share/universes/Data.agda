
module Data where

open import Meta

data Desc : Set₁ where
  done : Desc
  ind  : Desc → Desc
  sig  : (S : Set) (f : S → Desc) → Desc

[_] : Desc → Set → Set
[ done ] X = X
[ ind D ] X = X × [ D ] X
[ sig S f ] X = Σ S (λ x → [ f x ] X)

data Fix (D : Desc) : Set where
  con : [ D ] (Fix D) → Fix D

mutual
  data U : Set where
    Π : (s : U) (f : T s → U) → U
    μ : desc → U
    top : U

  data desc : Set where
    done : desc
    ind  : desc → desc
    case : (n : ℕ) (c : Fin n → desc) → desc
    sig  : (s : U) (f : T s → desc) → desc

  ⟦_⟧ : desc → Desc
  ⟦   done   ⟧ = done
  ⟦   ind D  ⟧ = ind ⟦ D ⟧
  ⟦ case n c ⟧ = sig (Fin n) (λ i → ⟦ c i ⟧)
  ⟦  sig s f ⟧ = sig (T s) (λ x → ⟦ f x ⟧)

  T : U → Set
  T (Π s f) = (S : T s) → T (f S)
  T (μ D)   = Fix ⟦ D ⟧
  T top     = ⊤
