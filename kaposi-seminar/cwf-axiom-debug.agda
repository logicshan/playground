module cwf-axiom-debug where

open import Relation.Binary.PropositionalEquality hiding (subst-subst-sym)
open ≡-Reasoning

-- heterogeneous equality
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
           → true [ σ ]t ≡ subst (Tm Γ) (sym Bool[]) true
  false[] : {Γ Δ : Con}{σ : Sub Γ Δ}
            → false [ σ ]t ≡ subst (Tm Γ) (sym Bool[]) false
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
--  Π[] : {Γ Δ : Con}{σ : Sub Γ Δ}{A : Ty Δ}{B : Ty (Δ ▷ A)}
--        → (Π A B) [ σ ]T ≡ Π (A [ σ ]T) ((B [ σ ∘ p , q ]T))
--  lam[] : {Γ Δ : Con}{σ : Sub Γ Δ}{A : Ty Δ}{B : Ty (Δ ▷ A)}{t : Tm (Δ ▷ A) B}
--        → (lam t) [ σ ]t ≡ subst (Tm Γ) (sym Π[]) (lam (t [ σ ∘ p , q ]t))

{- Standard lemma used in rewriting substitutions.
   It expresses that substituting with the inverse and then with the original path
   is the identity. -}
subst-subst-sym : ∀ {a b} {A : Set} (P : A → Set) {x y : A}
                  (p : x ≡ y)
                  (u : P x)
                  → subst P (sym p) (subst P p u) ≡ u
subst-subst-sym P refl u = refl

-- We reuse the following definitions from the original file.
⓪ : {Γ : Con} {A : Ty Γ} → Tm (Γ ▷ A) (A [ p ]T)
⓪ = q

① : {Γ : Con}{A : Ty Γ}{B : Ty (Γ ▷ A)} → Tm (Γ ▷ A ▷ B) (A [ p ]T [ p ]T)
① = q [ p ]t

-- The problematic function f:

f : {Γ Δ : Con}{A : Ty Δ}{B : Ty (Δ ▷ A)}
    → (σ : Sub Γ Δ)
    → Sub (Γ ▷ (A [ σ ]T) ▷ B [ (σ ∘ p) , subst (Tm _) (sym [∘]) q ]T) (Δ ▷ A ▷ B)
f {Γ = Γ}{A = A}{B = B} σ =
  σ ∘ p ∘ p ,
    subst (Tm _) (sym helper₁) ① ,
    subst (Tm _) helper₂ ⓪
  where
    -- helper₁ relates the two different ways to substitute in type A.
    helper₁ : A [ σ ∘ p ∘ p ]T ≡ A [ σ ]T [ p ]T [ p ]T
    helper₁ = begin
      A [ σ ∘ p ∘ p ]T
        ≡⟨ [∘] ⟩
      A [ σ ∘ p ]T [ p ]T
        ≡⟨ cong (λ x → x [ p ]T) [∘] ⟩
      A [ σ ]T [ p ]T [ p ]T ∎

    -- Instead of using (sym [∘]) on one side and (sym helper₁) on the other side,
    -- we use the standard lemma subst-subst-sym to reconcile them.
    helper₂ : B [ (σ ∘ p) , subst (Tm (Γ ▷ A [ σ ]T)) (sym [∘]) q ]T [ p ]T ≡
              B [ σ ∘ p ∘ p , subst (Tm _) (sym helper₁) ① ]T
    helper₂ = begin
      B [ (σ ∘ p) , subst (Tm (Γ ▷ A [ σ ]T)) (sym [∘]) q ]T [ p ]T
        ≡⟨ [∘] ⟨
             -- By the properties of substitution composition (using ,∘)
      B [ (σ ∘ p , subst (Tm (Γ ▷ A [ σ ]T)) (sym [∘]) q) ∘ p ]T
        ≡⟨ cong (λ x → B [ x ]T) (,∘ {t = subst (Tm _) (sym [∘]) q}) ⟩
      B [ σ ∘ p ∘ p , subst (Tm _) (sym [∘]) (subst (Tm _) (sym [∘]) q [ p ]t) ]T
        ≡⟨
          -- Now we apply the lemma subst-subst-sym to rewrite the double substitution,
          -- using helper₁ to bridge the gap between (sym [∘]) and (sym helper₁).
          cong (λ t → B [ σ ∘ p ∘ p , t ]T)
          (subst-subst-sym (λ X → Tm (Γ ▷ A [ σ ]T) X) (sym [∘]) _
             ∙   -- the underscore marks the appropriate term, which should be q [ p ]t
          )
        ⟩
      B [ σ ∘ p ∘ p , subst (Tm _) (sym helper₁) ① ]T ∎

{- Note:
   In the above, the use of "subst-subst-sym" with an underscore (_) indicates a place where
   you might need to provide a more concrete term or further adjust the chain of equalities.
   The idea is to show that substituting by (sym [∘]) and then by [∘] in this context is equal
   to doing nothing, up to the helper₁ rewrite. Depending on your overall setup this part might
   need a more detailed derivation.

   Also, remember that the types of the substitution chains must match exactly. If further
   restructuring is necessary, you might have to introduce additional helper lemmas
   to manage the rewriting properly.
-}
