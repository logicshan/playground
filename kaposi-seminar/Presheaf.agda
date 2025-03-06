{-# OPTIONS --without-K #-}

module Presheaf where

open import Relation.Binary.PropositionalEquality

-- Basic declarations for the contextual category
postulate
  Con : Set
  Sub : Con → Con → Set
  Ty  : Con → Set
  Tm  : (Γ : Con) → Ty Γ → Set

-- Category structure
postulate
  _∘_ : {Γ Θ Δ : Con} → Sub Θ Δ → Sub Γ Θ → Sub Γ Δ
  id  : {Γ : Con} → Sub Γ Γ

infixl 7 _∘_

-- Substitution action
postulate
  _[_]ᵗʸ : {Γ Δ : Con} → Ty Δ → Sub Γ Δ → Ty Γ
  _[_]ᵗᵐ : {Γ Δ : Con} {A : Ty Δ} → 
           Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]ᵗʸ)

-- Empty context and its constructor
postulate
  ∙   : Con
  ε   : {Γ : Con} → Sub Γ ∙

-- Context extension
postulate
  _▷_ : (Γ : Con) → Ty Γ → Con
  _,_ : {Γ Δ : Con} {A : Ty Δ} → 
        (σ : Sub Γ Δ) → Tm Γ (A [ σ ]ᵗʸ) → Sub Γ (Δ ▷ A)
  p   : {Γ : Con} {A : Ty Γ} → Sub (Γ ▷ A) Γ
  q   : {Γ : Con} {A : Ty Γ} → Tm (Γ ▷ A) (A [ p ]ᵗʸ)

-- Categorical laws
postulate
  ass : {Γ Θ Δ Ξ : Con} {σ : Sub Θ Δ} {δ : Sub Γ Θ} {ν : Sub Ξ Γ} →
        (σ ∘ δ) ∘ ν ≡ σ ∘ (δ ∘ ν)
  idl : {Γ Δ : Con} {σ : Sub Γ Δ} → id ∘ σ ≡ σ
  idr : {Γ Δ : Con} {σ : Sub Γ Δ} → σ ∘ id ≡ σ

-- Substitution laws
postulate
  [∘]  : {Γ Δ Θ : Con} {A : Ty Θ} {σ : Sub Δ Θ} {δ : Sub Γ Δ} →
         A [ σ ∘ δ ]ᵗʸ ≡ A [ σ ]ᵗʸ [ δ ]ᵗʸ
  [id] : {Γ : Con} {A : Ty Γ} → A [ id ]ᵗʸ ≡ A
  
-- Context laws
postulate
  ∙η  : {Γ : Con} {σ : Sub Γ ∙} → σ ≡ ε
  ▷β₁ : {Γ Δ : Con} {A : Ty Δ} {σ : Sub Γ Δ} {t : Tm Γ (A [ σ ]ᵗʸ)} →
        p ∘ (σ , t) ≡ σ
  ▷β₂ : {Γ Δ : Con} {A : Ty Δ} {σ : Sub Γ Δ} {t : Tm Γ (A [ σ ]ᵗʸ)} →
        q [ σ , t ]ᵗᵐ ≡ t
  ▷η  : {Γ : Con} {A : Ty Γ} → (p , q) ≡ id
  ,∘  : {Γ Δ Θ : Con} {A : Ty Θ} {σ : Sub Δ Θ} {t : Tm Δ (A [ σ ]ᵗʸ)} 
        {δ : Sub Γ Δ} →
        (σ , t) ∘ δ ≡ (σ ∘ δ , t [ δ ]ᵗᵐ)

-- Bool type and its operations
postulate
  Bool  : {Γ : Con} → Ty Γ
  true  : {Γ : Con} → Tm Γ Bool
  false : {Γ : Con} → Tm Γ Bool
  ite   : {Γ : Con} {C : Ty (Γ ▷ Bool)} →
          (t : Tm Γ Bool) → 
          Tm Γ (C [ id , true ]ᵗʸ) → 
          Tm Γ (C [ id , false ]ᵗʸ) → 
          Tm Γ (C [ id , t ]ᵗʸ)

-- Bool computation and substitution rules
postulate
  Boolβ₁  : {Γ : Con} {C : Ty (Γ ▷ Bool)} 
            {u : Tm Γ (C [ id , true ]ᵗʸ)} 
            {v : Tm Γ (C [ id , false ]ᵗʸ)} →
            ite true u v ≡ u
  Boolβ₂  : {Γ : Con} {C : Ty (Γ ▷ Bool)} 
            {u : Tm Γ (C [ id , true ]ᵗʸ)} 
            {v : Tm Γ (C [ id , false ]ᵗʸ)} →
            ite false u v ≡ v
  Bool[]  : {Γ Δ : Con} {σ : Sub Γ Δ} →
            Bool [ σ ]ᵗʸ ≡ Bool
  true[]  : {Γ Δ : Con} {σ : Sub Γ Δ} →
            true [ σ ]ᵗᵐ ≡ true
  false[] : {Γ Δ : Con} {σ : Sub Γ Δ} →
            false [ σ ]ᵗᵐ ≡ false
  ite[]   : {Γ Δ : Con} {C : Ty (Δ ▷ Bool)} {σ : Sub Γ Δ}
            {t : Tm Δ Bool} {u : Tm Δ (C [ id , true ]ᵗʸ)} 
            {v : Tm Δ (C [ id , false ]ᵗʸ)} →
            (ite t u v) [ σ ]ᵗᵐ ≡ ite (t [ σ ]ᵗᵐ) (u [ σ ]ᵗᵐ) (v [ σ ]ᵗᵐ)

-- Dependent function type and its operations
postulate
  Π   : {Γ : Con} → (A : Ty Γ) → Ty (Γ ▷ A) → Ty Γ
  lam : {Γ : Con} {A : Ty Γ} {B : Ty (Γ ▷ A)} →
        Tm (Γ ▷ A) B → Tm Γ (Π A B)
  app : {Γ : Con} {A : Ty Γ} {B : Ty (Γ ▷ A)} →
        Tm Γ (Π A B) → Tm (Γ ▷ A) B

-- Π-type computation and substitution rules
postulate
  Πβ   : {Γ : Con} {A : Ty Γ} {B : Ty (Γ ▷ A)} 
         {t : Tm (Γ ▷ A) B} →
         app (lam t) ≡ t
  Πη   : {Γ : Con} {A : Ty Γ} {B : Ty (Γ ▷ A)} 
         {t : Tm Γ (Π A B)} →
         lam (app t) ≡ t
  Π[]  : {Γ Δ : Con} {A : Ty Δ} {B : Ty (Δ ▷ A)} 
         {σ : Sub Γ Δ} →
         (Π A B) [ σ ]ᵗʸ ≡ Π (A [ σ ]ᵗʸ) (B [ σ ∘ p , q ]ᵗʸ)
  lam[] : {Γ Δ : Con} {A : Ty Δ} {B : Ty (Δ ▷ A)} 
          {t : Tm (Δ ▷ A) B} {σ : Sub Γ Δ} →
          (lam t) [ σ ]ᵗᵐ ≡ lam (t [ σ ∘ p , q ]ᵗᵐ)


infixl 6 _[_]ᵗʸ _[_]ᵗᵐ
infixl 5 _,_
