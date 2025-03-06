module CwF where

open import Relation.Binary.PropositionalEquality
--open ≡-Reasoning

-- heterogenous equality
infix 2 _⊢_≡[_]≡_
data _⊢_≡[_]≡_ {X : Set}(F : X → Set) : {x y : X} → F x → x ≡ y → F y → Set where
  refl : {x : X}{z : F x} → F ⊢ z ≡[ refl ]≡ z

record CwF : Set₁ where
  infixl 7 _∘_
  infixl 6 _[_]T _[_]t
  infixl 5 _▷_

  field
    Con : Set
    Sub : Con → Con → Set
    Ty  : Con → Set
    Tm  : (Γ : Con) → Ty Γ → Set
    _∘_ : {Γ Θ Δ : Con} → Sub Θ Δ → Sub Γ Θ → Sub Γ Δ
    id  : {Γ : Con} → Sub Γ Γ
    _[_]T : {Γ Δ : Con} → Ty Δ → Sub Γ Δ → Ty Γ
    _[_]t : {Γ Δ : Con}{A : Ty Δ} → Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
    ∙ : Con
    ε : {Γ : Con} → Sub Γ ∙
    _▷_ : (Γ : Con) → Ty Γ → Con
    _,_ : {Γ Δ : Con}{A : Ty Δ} → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T) → Sub Γ (Δ ▷ A)
    p : {Γ : Con}{A : Ty Γ} → Sub (Γ ▷ A) Γ
    q : {Γ : Con}{A : Ty Γ} → Tm (Γ ▷ A) (A [ p ]T)
    ass : {Γ Δ Θ Ξ : Con}{σ : Sub Θ Ξ}{δ : Sub Δ Θ}{ν : Sub Γ Δ}
          → (σ ∘ δ) ∘ ν ≡ σ ∘ (δ ∘ ν)
    idl : {Γ Δ : Con} → (σ : Sub Γ Δ) → id ∘ σ ≡ σ
    idr : {Γ Δ : Con} → (σ : Sub Γ Δ) → σ ∘ id ≡ σ
    [∘] : {Γ Δ Θ : Con}{A : Ty Θ} → {σ : Sub Δ Θ} → {δ : Sub Γ Δ}
          → A [ σ ∘ δ ]T ≡ A [ σ ]T [ δ ]T
    [id] : {Γ : Con}{A : Ty Γ} → A [ id ]T ≡ A
    ∙η  : {Γ : Con}{σ : Sub Γ ∙} → σ ≡ ε
    ▷β₁ : {Γ Δ : Con}{A : Ty Δ}{σ : Sub Γ Δ}{t : Tm Γ (A [ σ ]T)}
          → p ∘ (σ , t) ≡ σ
    ▷β₂ : {Γ Δ : Con}{A : Ty Δ}{σ : Sub Γ Δ}{t : Tm Γ (A [ σ ]T)}
          → (λ δ → Tm Γ (A [ δ ]T)) ⊢ subst (Tm Γ) (sym [∘]) (q [ σ , t ]t) ≡[ ▷β₁ ]≡ t
    ▷η  : {Γ : Con}{A : Ty Γ} → (p , q) ≡ id {Γ ▷ A}
    ,∘  : {Γ Δ Θ : Con}{A : Ty Θ}{σ : Sub Δ Θ}{δ : Sub Γ Δ}{t : Tm Δ (A [ σ ]T)}
          → (σ , t) ∘ δ ≡ ((σ ∘ δ) , (subst (Tm Γ) (sym [∘]) (t [ δ ]t)))
