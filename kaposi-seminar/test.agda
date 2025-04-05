open import Relation.Binary.PropositionalEquality hiding (subst-subst-sym)
open ≡-Reasoning

-- heterogenous equality
infix 2 _⊢_≡[_]≡_
data _⊢_≡[_]≡_ {X : Set}(F : X → Set) : {x y : X} → F x → x ≡ y → F y → Set where
  refl : {x : X}{z : F x} → F ⊢ z ≡[ refl ]≡ z

infixl 7 _∘_
infixl 6 _[_]T _[_]t
infixl 5 _▷_
infixl 4 _,_

postulate
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
        → (σ , t) ∘ δ ≡ (σ ∘ δ , subst (Tm Γ) (sym [∘]) (t [ δ ]t))

postulate
  Bool :  {Γ : Con} → Ty Γ
  true  : {Γ : Con} → Tm Γ Bool
  false : {Γ : Con} → Tm Γ Bool
  ite : {Γ : Con}{C : Ty (Γ ▷ Bool)}
        → (t : Tm Γ Bool)
        → Tm Γ (C [ id , subst (Tm Γ) (sym [id]) true ]T)
        → Tm Γ (C [ id , subst (Tm Γ) (sym [id]) false ]T)
        → Tm Γ (C [ id , subst (Tm Γ) (sym [id]) t ]T)
  Boolβ₁ : {Γ : Con}
           {C : Ty (Γ ▷ Bool)}
           {u : Tm Γ (C [ id , subst (Tm Γ) (sym [id]) true ]T)}
           {v : Tm Γ (C [ id , subst (Tm Γ) (sym [id]) false ]T)}
           → ite true u v ≡ u

  Boolβ₂ : {Γ : Con}
           {C : Ty (Γ ▷ Bool)}
           {u : Tm Γ (C [ id , subst (Tm Γ) (sym [id]) true ]T)}
           {v : Tm Γ (C [ id , subst (Tm Γ) (sym [id]) false ]T)}
           → ite false u v ≡ v
  Bool[] : {Γ Δ : Con}{σ : Sub Γ Δ} → Bool [ σ ]T ≡ Bool
  true[] : {Γ Δ : Con}{σ : Sub Γ Δ}
           → true [ σ ]t
             ≡
             subst (Tm Γ) (sym Bool[]) true
  false[] : {Γ Δ : Con}{σ : Sub Γ Δ}
            → false [ σ ]t
              ≡
              subst (Tm Γ) (sym Bool[]) false

  ite[] : {Γ Δ : Con}
          {σ : Sub Γ Δ}
          {C : Ty (Δ ▷ Bool)}
          {t : Tm Δ Bool}
          {u : Tm Δ (C [ id , subst (Tm Δ) (sym [id]) true ]T)}
          {v : Tm Δ (C [ id , subst (Tm Δ) (sym [id]) false ]T)}
          → ite t u v ≡ ite t u v

  Π : {Γ : Con} → (A : Ty Γ) → Ty (Γ ▷ A) → Ty Γ
  lam : {Γ : Con}{A : Ty Γ}{B : Ty (Γ ▷ A)} → Tm (Γ ▷ A) B → Tm Γ (Π A B)
  app : {Γ : Con}{A : Ty Γ}{B : Ty (Γ ▷ A)} → Tm Γ (Π A B) → Tm (Γ ▷ A) B
  Πβ : {Γ : Con}{A : Ty Γ}{B : Ty (Γ ▷ A)}{t : Tm (Γ ▷ A) B} → app (lam t) ≡ t
  Πη : {Γ : Con}{A : Ty Γ}{B : Ty (Γ ▷ A)}{t : Tm Γ (Π A B)} → lam (app t) ≡ t
  Π[] : {Γ Δ : Con}{σ : Sub Γ Δ}{A : Ty Δ}{B : Ty (Δ ▷ A)}
--      → (Π A B) [ σ ]T ≡ Π (A [ σ ]T) (B [ σ ∘ p , q ]T)
        → (Π A B) [ σ ]T ≡ Π (A [ σ ]T) ((B [ σ ∘ p , subst (Tm (Γ ▷ A [ σ ]T)) (sym [∘]) q ]T))
  lam[] : {Γ Δ : Con}{σ : Sub Γ Δ}{A : Ty Δ}{B : Ty (Δ ▷ A)}{t : Tm (Δ ▷ A) B}
--        → (lam t) [ σ ]t ≡ lam (t [ σ ∘ p , q ]t)
          → (lam t) [ σ ]t ≡ subst (Tm Γ) (sym Π[]) (lam (t [ σ ∘ p , subst (Tm (Γ ▷ A [ σ ]T)) (sym [∘]) q ]t))

⓪ : {Γ : Con} {A : Ty Γ} → Tm (Γ ▷ A) (A [ p ]T)
⓪ = q

① : {Γ : Con}{A : Ty Γ}{B : Ty (Γ ▷ A)} → Tm (Γ ▷ A ▷ B) (A [ p ]T [ p ]T)
① = q [ p ]t

② : {Γ : Con}{A : Ty Γ}{B : Ty (Γ ▷ A)}{C : Ty (Γ ▷ A ▷ B)} → Tm (Γ ▷ A ▷ B ▷ C) (A [ p ]T [ p ∘ p ]T)
② = q [ p ∘ p ]t

ex : {Γ : Con}{A B C : Ty Γ} → Sub (Γ ▷ A ▷ B [ p ]T ▷ C [ p ∘ p ]T) (Γ ▷ B ▷ C [ p ]T ▷ A [ p ∘ p ]T)
ex {Γ} {A} {B} {C} = id ∘ p ∘ p ∘ p ,
                     subst (Tm _) helper₁ ① ,
                     subst (Tm _) helper₂ ⓪ ,
                     subst (Tm _) helper₃ ②
  where
  helper₁ : (B [ p ]T [ p ]T [ p ]T) ≡ (B [ id ∘ p ∘ p ∘ p ]T)
  helper₁ = begin
    (B [ p ]T [ p ]T [ p ]T)
      ≡⟨ cong (λ x → x [ p ]T [ p ]T [ p ]T) [id] ⟨
    (B [ id ]T [ p ]T [ p ]T [ p ]T)
      ≡⟨ cong (λ x → x [ p ]T [ p ]T) [∘] ⟨
    (B [ id ∘ p ]T [ p ]T [ p ]T)
      ≡⟨ cong (λ x → x [ p ]T) [∘] ⟨
    (B [ id ∘ p ∘ p ]T [ p ]T)
      ≡⟨ [∘] ⟨
    (B [ id ∘ p ∘ p ∘ p ]T) ∎
  helper₂ : C [ p ∘ p ]T [ p ]T
            ≡
            C [ p ]T [ id ∘ p ∘ p ∘ p , subst (Tm (Γ ▷ A ▷ B [ p ]T ▷ C [ p ∘ p ]T)) helper₁ ① ]T
  helper₂ = begin
              C [ p ∘ p ]T [ p ]T
                ≡⟨ cong (λ x → x [ p ]T) [∘] ⟩
              C [ p ]T [ p ]T [ p ]T
                ≡⟨ cong (λ x → x [ p ]T [ p ]T [ p ]T) [id] ⟨
              C [ id ]T [ p ]T [ p ]T [ p ]T
                ≡⟨ cong (λ x → x [ p ]T [ p ]T) [∘] ⟨
              C [ id ∘ p ]T [ p ]T [ p ]T
                ≡⟨ cong (λ x → x [ p ]T) [∘] ⟨
              C [ id ∘ p ∘ p ]T [ p ]T
                ≡⟨ [∘] ⟨
              C [ id ∘ p ∘ p ∘ p ]T
                ≡⟨ cong (λ x → C [ x ]T) ▷β₁ ⟨
              C [ p ∘ (id ∘ p ∘ p ∘ p , _) ]T
                ≡⟨ [∘] ⟩
              C [ p ]T [ id ∘ p ∘ p ∘ p , subst (Tm (Γ ▷ A ▷ B [ p ]T ▷ C [ p ∘ p ]T)) helper₁ ① ]T ∎
  helper₃ : A [ p ]T [ p ∘ p ]T ≡
      A [ p ∘ p ]T [
      id ∘ p ∘ p ∘ p ,
      subst (Tm (Γ ▷ A ▷ B [ p ]T ▷ C [ p ∘ p ]T)) helper₁ ①
      , subst (Tm (Γ ▷ A ▷ B [ p ]T ▷ C [ p ∘ p ]T)) helper₂ ⓪
      ]T
  helper₃ = begin
    A [ p ]T [ p ∘ p ]T
      ≡⟨ [∘] ⟨
    A [ p ∘ (p ∘ p) ]T
      ≡⟨ cong (λ x → A [ x ]T) ass ⟨
    A [ p ∘ p ∘ p ]T
      ≡⟨ cong (λ x → x [ p ∘ p ∘ p ]T) [id] ⟨
    A [ id ]T [ p ∘ p ∘ p ]T
      ≡⟨ [∘] ⟨
    A [ id ∘ (p ∘ p ∘ p) ]T
      ≡⟨ cong (λ x → A [ x ]T) ass ⟨
    A [ id ∘ (p ∘ p) ∘ p ]T
      ≡⟨ cong (λ x → A [ x ∘ p ]T) ass ⟨
    A [ id ∘ p ∘ p ∘ p ]T
      ≡⟨ cong (λ x → A [ x ]T) ▷β₁ ⟨
    A [ p ∘ (id ∘ p ∘ p ∘ p , _) ]T
      ≡⟨ cong (λ x → A [ p ∘ x ]T) ▷β₁ ⟨
    A [ p ∘ (p ∘ (id ∘ p ∘ p ∘ p , _ , _)) ]T
      ≡⟨ cong (λ x → A [ x ]T) ass ⟨
    A [ p ∘ p ∘ (id ∘ p ∘ p ∘ p , _ , _) ]T
      ≡⟨ [∘] ⟩
    A [ p ∘ p ]T [ id ∘ p ∘ p ∘ p ,
        subst (Tm (Γ ▷ A ▷ B [ p ]T ▷ C [ p ∘ p ]T)) helper₁ ①
      , subst (Tm (Γ ▷ A ▷ B [ p ]T ▷ C [ p ∘ p ]T)) helper₂ ⓪
      ]T ∎


ex' : {A B C : Ty ∙} → Sub (∙ ▷ A ▷ B [ p ]T ▷ C [ p ∘ p ]T) (∙ ▷ B ▷ C [ p ]T ▷ A [ p ∘ p ]T)
ex' {A} {B} {C} = ε ,
                 subst (Tm _) helper₁ ① ,
                 subst (Tm _) helper₂ ⓪ ,
                 subst (Tm _) helper₃ ②
  where
  helper₁ : (B [ p ]T [ p ]T [ p ]T) ≡ (B [ ε ]T)
  helper₁ = begin
    (B [ p ]T [ p ]T [ p ]T)
      ≡⟨ cong (λ x → x [ p ]T) (sym [∘]) ⟩
    (B [ p ∘ p ]T [ p ]T)
      ≡⟨ cong (λ x → B [ x ]T [ p ]T) ∙η ⟩
    (B [ ε ]T [ p ]T)
      ≡⟨ [∘] ⟨
    (B [ ε ∘ p ]T)
      ≡⟨ cong (λ x → B [ x ]T) ∙η ⟩
    (B [ ε ]T) ∎
  helper₂ : (C [ p ∘ p ]T [ p ]T)
            ≡ (C [ p ]T [ ε , subst (Tm (∙ ▷ A ▷ B [ p ]T ▷ C [ p ∘ p ]T)) helper₁ ① ]T)
  helper₂ = begin
    (C [ p ∘ p ]T [ p ]T)
      ≡⟨ cong (λ x → C [ x ]T [ p ]T) ∙η ⟩
    (C [ ε ]T [ p ]T)
      ≡⟨ [∘] ⟨
    (C [ ε ∘ p ]T)
      ≡⟨ cong (λ x → C [ x ]T) ∙η ⟩
    (C [ ε ]T)
      ≡⟨ cong (λ x → C [ x ]T) ∙η ⟨
    (C [ p ∘ _ ]T)
      ≡⟨ [∘] ⟩
    (C [ p ]T [ _ ]T) ∎
  helper₃ : A [ p ]T [ p ∘ p ]T ≡
      A [ p ∘ p ]T [
      ε , subst (Tm (∙ ▷ A ▷ B [ p ]T ▷ C [ p ∘ p ]T)) helper₁ ① ,
      subst (Tm (∙ ▷ A ▷ B [ p ]T ▷ C [ p ∘ p ]T)) helper₂ ⓪
      ]T
  helper₃ = begin
    A [ p ]T [ p ∘ p ]T
      ≡⟨ [∘] ⟨
    A [ p ∘ (p ∘ p) ]T
      ≡⟨ cong (λ x → A [ x ]T) ∙η ⟩
    A [ ε ]T
      ≡⟨ cong (λ x → A [ x ]T) ∙η ⟨
    A [ ε ∘ _ ]T
      ≡⟨ [∘] ⟩
    A [ ε ]T [ _ ]T
      ≡⟨ cong (λ x → A [ x ]T [ ε , subst (Tm (∙ ▷ A ▷ B [ p ]T ▷ C [ p ∘ p ]T)) helper₁ ① , subst (Tm (∙ ▷ A ▷ B [ p ]T ▷ C [ p ∘ p ]T)) helper₂ ⓪ ]T) ∙η ⟨
    A [ p ∘ p ]T [ ε , subst (Tm (∙ ▷ A ▷ B [ p ]T ▷ C [ p ∘ p ]T)) helper₁ ① , subst (Tm (∙ ▷ A ▷ B [ p ]T ▷ C [ p ∘ p ]T)) helper₂ ⓪ ]T ∎

f : {Γ Δ : Con}{A : Ty Δ}{B : Ty (Δ ▷ A)}
    → (σ : Sub Γ Δ)
    → Sub (Γ ▷ (A [ σ ]T) ▷ B [ (σ ∘ p) , subst (Tm _) (sym [∘]) q ]T) (Δ ▷ A ▷ B)
f {Γ = Γ}{A = A}{B = B} σ = σ ∘ p ∘ p ,
                            subst (Tm _) helper₁ ① ,
                            subst (Tm _) helper₂ ⓪ 
  where
  helper₁ : A [ σ ]T [ p ]T [ p ]T ≡ A [ σ ∘ p ∘ p ]T
  helper₁ = sym (trans [∘] (cong (λ x → x [ p ]T) [∘]))

  helper₂ : (B [ σ ∘ p , subst (Tm (Γ ▷ A [ σ ]T)) (sym [∘]) q ]T [ p ]T)
            ≡
            (B [
               σ ∘ p ∘ p ,
               subst
               (Tm
                (Γ ▷ A [ σ ]T ▷
                 B [ σ ∘ p , subst (Tm (Γ ▷ A [ σ ]T)) (sym [∘]) q ]T))
               helper₁ ①
               ]T)
  helper₂ = {!!}
