\begin{code}
{-# OPTIONS --prop --rewriting #-}
module Def.DepModel where

open import Lib
open import Def.Syntax

record DepModel {i j} : Set (lsuc (i ⊔ j)) where
  infixl 6 _[_]∙
  infixl 5 _▹∙_
  infixl 7 _+o∙_

  field
    Ty∙        : Ty → Set i
    Nat∙       : Ty∙ Nat
    Bool∙      : Ty∙ Bool

    Con∙       : Con → Set i
    ◇∙         : Con∙ ◇
    _▹∙_       : ∀{Γ A} → Con∙ Γ → Ty∙ A → Con∙ (Γ ▹ A)

    Var∙       : ∀{Γ A} → Con∙ Γ → Ty∙ A → Var Γ A → Set j
    vz∙        : ∀{Γ A}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ A} → Var∙ {Γ ▹ A} (Γ∙ ▹∙ A∙) A∙ vz
    vs∙        : ∀{Γ A B}{x : Var Γ A}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ A}{B∙ : Ty∙ B} →
                 Var∙ Γ∙ A∙ x → Var∙ {Γ ▹ B} (Γ∙ ▹∙ B∙) A∙ (vs x)

    Tm∙        : ∀{Γ A} → Con∙ Γ → Ty∙ A → Tm Γ A → Set j

    Sub∙       : ∀{Δ Γ} → Con∙ Δ → Con∙ Γ → Sub Δ Γ → Set j
    p∙         : ∀{Γ A}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ A} → Sub∙ (Γ∙ ▹∙ A∙) Γ∙ p
    ⟨_⟩∙       : ∀{Γ A}{t : Tm Γ A}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ A} → Tm∙ Γ∙ A∙ t → Sub∙ Γ∙ (Γ∙ ▹∙ A∙) ⟨ t ⟩
    _⁺∙        : ∀{Γ Δ A}{σ : Sub Δ Γ}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{A∙ : Ty∙ A}
                 (σ∙ : Sub∙ Δ∙ Γ∙ σ) → Sub∙ (Δ∙ ▹∙ A∙) (Γ∙ ▹∙ A∙) (σ ⁺)

    var∙       : ∀{Γ A}{x : Var Γ A}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ A} → Var∙ Γ∙ A∙ x → Tm∙ Γ∙ A∙ (var x)
    _[_]∙      : ∀{Γ Δ A}{t : Tm Γ A}{σ : Sub Δ Γ}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{A∙ : Ty∙ A} → 
                 Tm∙ Γ∙ A∙ t → Sub∙ Δ∙ Γ∙ σ → Tm∙ Δ∙ A∙ (t [ σ ])
    [p]∙       : ∀{Γ A B}{x : Var Γ A}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ A}{B∙ : Ty∙ B}{x∙ : Var∙ Γ∙ A∙ x} →
                 (Tm∙ (Γ∙ ▹∙ B∙) A∙ ~) [p] (var∙ x∙ [ p∙ ]∙) (var∙ (vs∙ x∙))
    vz[⟨⟩]∙    : ∀{Γ A}{t : Tm Γ A}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ A}{t∙ : Tm∙ Γ∙ A∙ t} →
                 (Tm∙ Γ∙ A∙ ~) vz[⟨⟩] (var∙ vz∙ [ ⟨ t∙ ⟩∙ ]∙) t∙
    vz[⁺]∙     : ∀{Γ Δ A}{σ : Sub Δ Γ}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{A∙ : Ty∙ A}{σ∙ : Sub∙ Δ∙ Γ∙ σ} →
                 (Tm∙ (Δ∙ ▹∙ A∙) A∙ ~) vz[⁺] (var∙ vz∙ [ σ∙ ⁺∙ ]∙) (var∙ vz∙)
    vs[⟨⟩]∙    : ∀{Γ A B}{x : Var Γ A}{t : Tm Γ B}
                 {Γ∙ : Con∙ Γ}{A∙ : Ty∙ A}{B∙ : Ty∙ B}{x∙ : Var∙ Γ∙ A∙ x}{t∙ : Tm∙ Γ∙ B∙ t} →
                 (Tm∙ Γ∙ A∙ ~) vs[⟨⟩] (var∙ (vs∙ x∙) [ ⟨ t∙ ⟩∙ ]∙) (var∙ x∙)
    vs[⁺]∙     : ∀{Γ Δ A B}{x : Var Γ A}{σ : Sub Δ Γ}
                 {Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{A∙ : Ty∙ A}{B∙ : Ty∙ B}{x∙ : Var∙ Γ∙ A∙ x}{σ∙ : Sub∙ Δ∙ Γ∙ σ} →
                 (Tm∙ (Δ∙ ▹∙ B∙) A∙ ~) vs[⁺] (var∙ (vs∙ x∙) [ σ∙ ⁺∙ ]∙) (var∙ x∙ [ σ∙ ]∙ [ p∙ ]∙)

    true∙      : ∀{Γ}{Γ∙ : Con∙ Γ} → Tm∙ Γ∙ Bool∙ true
    false∙     : ∀{Γ}{Γ∙ : Con∙ Γ} → Tm∙ Γ∙ Bool∙ false
    ite∙       : ∀{Γ A}{t : Tm Γ Bool}{u v : Tm Γ A}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ A} →
                 Tm∙ Γ∙ Bool∙ t → Tm∙ Γ∙ A∙ u → Tm∙ Γ∙ A∙ v → Tm∙ Γ∙ A∙ (ite t u v)
    iteβ₁∙     : ∀{Γ A}{u v : Tm Γ A}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ A}{u∙ : Tm∙ Γ∙ A∙ u}{v∙ : Tm∙ Γ∙ A∙ v} →
                 (Tm∙ Γ∙ A∙ ~) iteβ₁ (ite∙ true∙ u∙ v∙) u∙
    iteβ₂∙     : ∀{Γ A}{u v : Tm Γ A}{Γ∙ : Con∙ Γ}{A∙ : Ty∙ A}{u∙ : Tm∙ Γ∙ A∙ u}{v∙ : Tm∙ Γ∙ A∙ v} →
                 (Tm∙ Γ∙ A∙ ~) iteβ₂ (ite∙ false∙ u∙ v∙) v∙
    true[]∙    : ∀{Γ Δ}{σ : Sub Δ Γ}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{σ∙ : Sub∙ Δ∙ Γ∙ σ} →
                 (Tm∙ Δ∙ Bool∙ ~) true[] (true∙ [ σ∙ ]∙) true∙
    false[]∙   : ∀{Γ Δ}{σ : Sub Δ Γ}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{σ∙ : Sub∙ Δ∙ Γ∙ σ} →
                 (Tm∙ Δ∙ Bool∙ ~) false[] (false∙ [ σ∙ ]∙) false∙
    ite[]∙     : ∀{Γ Δ A}{t : Tm Γ Bool}{u v : Tm Γ A}{σ : Sub Δ Γ}
                 {Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{A∙ : Ty∙ A}{t∙ : Tm∙ Γ∙ Bool∙ t}
                 {u∙ : Tm∙ Γ∙ A∙ u}{v∙ : Tm∙ Γ∙ A∙ v}{σ∙ : Sub∙ Δ∙ Γ∙ σ} →
                 (Tm∙ Δ∙ A∙ ~) ite[] (ite∙ t∙ u∙ v∙ [ σ∙ ]∙) (ite∙ (t∙ [ σ∙ ]∙) (u∙ [ σ∙ ]∙) (v∙ [ σ∙ ]∙))
    
    num∙       : ∀{Γ}{Γ∙ : Con∙ Γ}(n : ℕ) → Tm∙ Γ∙ Nat∙ (num n)
    isZero∙    : ∀{Γ}{t : Tm Γ Nat}{Γ∙ : Con∙ Γ} → Tm∙ Γ∙ Nat∙ t → Tm∙ Γ∙ Bool∙ (isZero t)
    _+o∙_      : ∀{Γ}{u v : Tm Γ Nat}{Γ∙ : Con∙ Γ} → Tm∙ Γ∙ Nat∙ u → Tm∙ Γ∙ Nat∙ v → Tm∙ Γ∙ Nat∙ (u +o v)
    isZeroβ₁∙  : ∀{Γ}{Γ∙ : Con∙ Γ} → (Tm∙ Γ∙ Bool∙ ~) isZeroβ₁ (isZero∙ (num∙ 0)) true∙
    isZeroβ₂∙  : ∀{Γ}{Γ∙ : Con∙ Γ}{n : ℕ} → (Tm∙ Γ∙ Bool∙ ~) isZeroβ₂ (isZero∙ (num∙ (1 + n))) false∙
    +β∙        : ∀{Γ}{Γ∙ : Con∙ Γ}{m n : ℕ} → (Tm∙ Γ∙ Nat∙ ~) +β (num∙ m +o∙ num∙ n) (num∙ (m + n))
    num[]∙     : ∀{Γ Δ}{σ : Sub Δ Γ}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{σ∙ : Sub∙ Δ∙ Γ∙ σ}{n : ℕ} →
                 (Tm∙ Δ∙ Nat∙ ~) num[] (num∙ n [ σ∙ ]∙) (num∙ n)
    isZero[]∙  : ∀{Γ Δ}{t : Tm Γ Nat}{σ : Sub Δ Γ}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}{t∙ : Tm∙ Γ∙ Nat∙ t}{σ∙ : Sub∙ Δ∙ Γ∙ σ} →
                 (Tm∙ Δ∙ Bool∙ ~) isZero[] (isZero∙ t∙ [ σ∙ ]∙) (isZero∙ (t∙ [ σ∙ ]∙))
    +[]∙       : ∀{Γ Δ}{u v : Tm Γ Nat}{σ : Sub Δ Γ}{Γ∙ : Con∙ Γ}{Δ∙ : Con∙ Δ}
                 {u∙ : Tm∙ Γ∙ Nat∙ u}{v∙ : Tm∙ Γ∙ Nat∙ v}{σ∙ : Sub∙ Δ∙ Γ∙ σ} →
                 (Tm∙ Δ∙ Nat∙ ~) +[] ((u∙ +o∙ v∙) [ σ∙ ]∙) ((u∙ [ σ∙ ]∙) +o∙ (v∙ [ σ∙ ]∙))

  ⟦_⟧T : (A : Ty) → Ty∙ A
  ⟦ Nat ⟧T = Nat∙
  ⟦ Bool ⟧T = Bool∙

  ⟦_⟧C : (Γ : Con) → Con∙ Γ
  ⟦ ◇ ⟧C = ◇∙
  ⟦ Γ ▹ A ⟧C = ⟦ Γ ⟧C ▹∙ ⟦ A ⟧T

  ⟦_⟧v : ∀{Γ A}(x : Var Γ A)  → Var∙ ⟦ Γ ⟧C ⟦ A ⟧T x
  ⟦ vz ⟧v = vz∙
  ⟦ vs x ⟧v = vs∙ ⟦ x ⟧v

  postulate
    ⟦_⟧t : ∀{Γ A}(t : Tm Γ A)  → Tm∙  ⟦ Γ ⟧C ⟦ A ⟧T t

  ⟦_⟧s : ∀{Γ Δ}(σ : Sub Δ Γ) → Sub∙ ⟦ Δ ⟧C  ⟦ Γ ⟧C  σ
  ⟦ p ⟧s = p∙
  ⟦ ⟨ t ⟩ ⟧s = ⟨ ⟦ t ⟧t ⟩∙
  ⟦ σ ⁺ ⟧s = ⟦ σ ⟧s ⁺∙

  postulate
    ⟦var⟧     : ∀{Γ A}  {x : Var Γ A}              → ⟦ var x   ⟧t ≈ var∙ ⟦ x ⟧v
    ⟦[]⟧      : ∀{Γ Δ A}{t :  Tm Γ A}{σ : Sub Δ Γ} → ⟦ t [ σ ] ⟧t ≈ ⟦ t ⟧t [ ⟦ σ ⟧s ]∙
    {-# REWRITE ⟦var⟧ ⟦[]⟧ #-}

    ⟦true⟧    : ∀{Γ} → ⟦ true  {Γ} ⟧t ≈ true∙
    ⟦false⟧   : ∀{Γ} → ⟦ false {Γ} ⟧t ≈ false∙
    ⟦ite⟧     : ∀{Γ A}{t : Tm Γ Bool}{u v : Tm Γ A} → 
                ⟦ ite {Γ} t u v ⟧t ≈ ite∙ ⟦ t ⟧t ⟦ u ⟧t ⟦ v ⟧t
    {-# REWRITE ⟦true⟧ ⟦false⟧ ⟦ite⟧ #-}

    ⟦num⟧     : ∀{Γ n}               → ⟦ num {Γ} n ⟧t ≈ num∙ n
    ⟦isZero⟧  : ∀{Γ}{  t : Tm Γ Nat} → ⟦ isZero t  ⟧t ≈ isZero∙ ⟦ t ⟧t
    ⟦+⟧       : ∀{Γ}{u v : Tm Γ Nat} → ⟦ u +o v    ⟧t ≈ ⟦ u ⟧t +o∙ ⟦ v ⟧t
    {-# REWRITE ⟦num⟧ ⟦isZero⟧ ⟦+⟧ #-}

record DepModelTmP {j} : Set (lsuc j) where
  infixl 6 _[_]∙
  infixl 7 _+o∙_

  field
    Var∙     : ∀ Γ A → Var Γ A → Prop j
    vz∙      : ∀{Γ A} → Var∙ (Γ ▹ A) A vz
    vs∙      : ∀{Γ A B}{x : Var Γ A} →
               Var∙ Γ A x → Var∙ (Γ ▹ B) A (vs x)

    Tm∙      : ∀ Γ A → Tm Γ A → Prop j

    var∙     : ∀{Γ A}{x : Var Γ A} → Var∙ Γ A x → Tm∙ Γ A (var x)
    _[_]∙    : ∀{Γ Δ A}{t : Tm Γ A} → 
               Tm∙ Γ A t → (σ : Sub Δ Γ) → Tm∙ Δ A (t [ σ ])

    true∙    : ∀{Γ} → Tm∙ Γ Bool true
    false∙   : ∀{Γ} → Tm∙ Γ Bool false
    ite∙     : ∀{Γ A}{t : Tm Γ Bool}{u v : Tm Γ A} →
               Tm∙ Γ Bool t → Tm∙ Γ A u → Tm∙ Γ A v → Tm∙ Γ A (ite t u v)
               
    num∙     : ∀{Γ}(n : ℕ) → Tm∙ Γ Nat (num n)
    isZero∙  : ∀{Γ}{t : Tm Γ Nat} → Tm∙ Γ Nat t → Tm∙ Γ Bool (isZero t)
    _+o∙_    : ∀{Γ}{u v : Tm Γ Nat} → Tm∙ Γ Nat u → Tm∙ Γ Nat v → Tm∙ Γ Nat (u +o v)

  D : DepModel
  D = record
    { Ty∙ = λ _ → Lift ⊤
    ; Nat∙ = _
    ; Bool∙ = _
    ; Con∙ = λ _ → Lift ⊤
    ; ◇∙ = _
    ; _▹∙_ = _
    ; Var∙ = λ {Γ}{A} _ _ x → Lift (Var∙ Γ A x)
    ; vz∙ = mk vz∙
    ; vs∙ = λ x∙ → mk (vs∙ (un x∙))
    ; Tm∙ = λ {Γ}{A} _ _ a → Lift (Tm∙ Γ A a)
    ; Sub∙ = λ _ _ _ → Raise (Lift ⊤)
    ; p∙ = _
    ; ⟨_⟩∙ = _
    ; _⁺∙ = _
    ; var∙ = λ x∙ → mk (var∙ (un x∙))
    ; _[_]∙ = λ {_}{_}{_}{_}{γ} t∙ _ → mk (un t∙ [ γ ]∙)
    ; [p]∙ = refl
    ; vz[⟨⟩]∙ = refl
    ; vz[⁺]∙ = refl
    ; vs[⟨⟩]∙ = refl
    ; vs[⁺]∙ = refl
    ; true∙ = mk true∙
    ; false∙ = mk false∙
    ; ite∙ = λ t∙ u∙ v∙ → mk (ite∙ (un t∙) (un u∙) (un v∙))
    ; iteβ₁∙ = refl
    ; iteβ₂∙ = refl
    ; true[]∙ = refl
    ; false[]∙ = refl
    ; ite[]∙ = refl
    ; num∙ = λ n → mk (num∙ n)
    ; isZero∙ = λ t∙ → mk (isZero∙ (un t∙))
    ; _+o∙_ = λ u∙ v∙ → mk (un u∙ +o∙ un v∙)
    ; isZeroβ₁∙ = refl
    ; isZeroβ₂∙ = refl
    ; +β∙ = refl
    ; num[]∙ = refl
    ; isZero[]∙ = refl
    ; +[]∙ = refl
    }
  module D = DepModel D

  ⟦_⟧v : ∀{Γ A}(x : Var Γ A) → Var∙ Γ A x
  ⟦ x ⟧v = un (D.⟦ x ⟧v)

  ⟦_⟧t : ∀{Γ A}(a : Tm Γ A) → Tm∙ Γ A a
  ⟦ a ⟧t = un (D.⟦ a ⟧t)

record DepModelTm▹P {j} : Set (lsuc j) where
  infixl 6 _[_⁺]∙ _[⟨_⟩]∙ _[p]∙
  infixl 7 _+o∙_

  field
    Var∙     : ∀ Γ A B → Var (Γ ▹ A) B → Prop j
    vz∙      : ∀{Γ A} → Var∙ Γ A A vz
    vs∙      : ∀{Γ A B}{x : Var Γ A} →
               Var∙ Γ B A (vs x)

    Tm∙      : ∀ Γ A B → Tm (Γ ▹ A) B → Prop j

    var∙     : ∀{Γ A B}{x : Var (Γ ▹ A) B} → Var∙ Γ A B x → Tm∙ Γ A B (var x)
    _[_⁺]∙   : ∀{Γ Δ A B}{t : Tm (Γ ▹ A) B} → 
               Tm∙ Γ A B t → (γ : Sub Δ Γ) → Tm∙ Δ A B (t [ γ ⁺ ])
    _[⟨_⟩]∙  : ∀{Γ A B C}{t : Tm (Γ ▹ A ▹ B) C} → 
               Tm∙ (Γ ▹ A) B C t → (u : Tm (Γ ▹ A) B) → Tm∙ Γ A C (t [ ⟨ u ⟩ ])
    _[p]∙    : ∀{Γ A B}(t : Tm Γ A) → Tm∙ Γ B A (t [ p ])

    true∙    : ∀{Γ A} → Tm∙ Γ A Bool true
    false∙   : ∀{Γ A} → Tm∙ Γ A Bool false
    ite∙     : ∀{Γ A B}{t : Tm (Γ ▹ A) Bool}{u v : Tm (Γ ▹ A) B} →
               Tm∙ Γ A Bool t → Tm∙ Γ A B u → Tm∙ Γ A B v → Tm∙ Γ A B (ite t u v)

    num∙     : ∀{Γ A}(n : ℕ) → Tm∙ Γ A Nat (num n)
    isZero∙  : ∀{Γ A}{t : Tm (Γ ▹ A) Nat} → Tm∙ Γ A Nat t → Tm∙ Γ A Bool (isZero t)
    _+o∙_    : ∀{Γ A}{u v : Tm (Γ ▹ A) Nat} → Tm∙ Γ A Nat u → Tm∙ Γ A Nat v → Tm∙ Γ A Nat (u +o v)

  D : DepModelTmP
  D = record
    { Var∙ = λ Γ A x → (Δ : Con)(B : Ty)(e : Γ ≡ Δ ▹ B) → Var∙ Δ B A (transp (λ z → Var z A) e x)
    ; vz∙ = λ { Δ B refl → vz∙ }
    ; vs∙ = λ { x∙ Δ B refl → vs∙ }
    ; Tm∙ = λ Γ A a → (Δ : Con)(B : Ty)(e : Γ ≡ Δ ▹ B) → Tm∙ Δ B A (transp (λ z → Tm z A) e a)
    ; var∙ = λ { t∙ Δ B refl → var∙ (t∙ Δ B refl) }
    ; _[_]∙ = λ { {Γ}{Δ}{A}{t} t∙ (γ ⁺) Θ B refl → t∙ _ B refl [ γ ⁺]∙ ; {Γ}{Δ}{A}{t} t∙ ⟨ u ⟩ Θ B refl → t∙ _ _ refl [⟨ u ⟩]∙ ; {Γ}{Δ}{A}{t} t∙ p Θ B refl → t [p]∙ }
    ; true∙ = λ { Δ B refl → true∙ {Δ}{B} }
    ; false∙ = λ { Δ B refl → false∙ {Δ}{B} }
    ; ite∙ = λ { t∙ u∙ v∙ Δ B refl → ite∙ (t∙ Δ B refl) (u∙ Δ B refl) (v∙ Δ B refl) }
    ; num∙ = λ { n Δ B refl → num∙ n }
    ; isZero∙ = λ { t∙ Δ B refl → isZero∙ (t∙ Δ B refl) }
    ; _+o∙_ = λ { u∙ v∙ Δ B refl → u∙ Δ B refl +o∙ v∙ Δ B refl }
    }
  module D = DepModelTmP D

  ⟦_⟧v : ∀{Γ A B}(x : Var (Γ ▹ A) B) → Var∙ Γ A B x
  ⟦_⟧v {Γ}{A}{B} x = D.⟦ x ⟧v Γ A refl 

  ⟦_⟧t : ∀{Γ A B}(a : Tm (Γ ▹ A) B) → Tm∙ Γ A B a
  ⟦_⟧t {Γ}{A}{B} a = D.⟦ a ⟧t Γ A refl 
{-
[p][⟨⟩] : ∀{Γ A B}{t : Tm Γ A}{u : Tm Γ B} → t [ p ] [ ⟨ u ⟩ ] ≡ t
[p][⟨⟩] {Γ}{A}{B}{t}{u} = D.⟦ t ⟧t {B}{u}
  where
    D : DepModelTmP
    D = record
      { Var∙ = λ Γ A x → ∀{B}{u : Tm Γ B} → var x [ p ] [ ⟨ u ⟩ ] ≡ var x
      ; vz∙ = λ {Γ}{A}{B}{u} → cong (_[ ⟨ u ⟩ ]) [p] ◾ vs[⟨⟩]
      ; vs∙ = λ {Γ}{A}{B}{x} x∙ {C}{u} → cong (_[ ⟨ u ⟩ ]) [p] ◾ vs[⟨⟩]
      ; Tm∙ = λ Γ A a → ∀{B}{u : Tm Γ B} → a [ p ] [ ⟨ u ⟩ ] ≡ a
      ; var∙ = λ e → e
      ; _[_]∙ = λ {Γ}{Δ}{A}{t} t∙ γ {B}{u} → {!!}
      ; true∙ = λ {Γ}{B}{u} → cong (_[ ⟨ u ⟩ ]) true[] ◾ true[]
      ; false∙ = λ {Γ}{B}{u} → cong (_[ ⟨ u ⟩ ]) false[] ◾ false[]
      ; ite∙ = {!!}
      ; num∙ = {!!}
      ; isZero∙ = {!!}
      ; _+o∙_ = {!!}
      }
    module D = DepModelTmP D

[⟨⟩][] : ∀{Γ A B}{t : Tm (Γ ▹ A) B}{u : Tm Γ A}{Δ}{γ : Sub Δ Γ} →
  t [ ⟨ u ⟩ ] [ γ ] ≡ t [ γ ⁺ ] [ ⟨ u [ γ ] ⟩ ]
[⟨⟩][] {Γ}{A}{B}{t}{u}{Δ}{γ} = {!!}
  where
    D : DepModelTm▹P
    D = record
      { Var∙ = λ Γ A B x → {u : Tm Γ A}{Δ : Con}{γ : Sub Δ Γ} → var x [ ⟨ u ⟩ ] [ γ ] ≡ var x [ γ ⁺ ] [ ⟨ u [ γ ] ⟩ ]
      ; vz∙ = λ {Γ}{A}{u}{Δ}{γ} → cong (_[ γ ]) vz[⟨⟩] ◾ vz[⟨⟩] ⁻¹ ◾ cong (_[ ⟨ u [ γ ] ⟩ ]) (vz[⁺] ⁻¹)
      ; vs∙ = λ {Γ}{A}{B}{x}{u}{Δ}{γ} → cong (_[ γ ]) vs[⟨⟩] ◾ {!!} ◾ cong (_[ ⟨ u [ γ ] ⟩ ]) (vs[⁺] ⁻¹)
      ; Tm∙ = {!!}
      ; var∙ = {!!}
      ; _[_⁺]∙ = {!!}
      ; _[⟨_⟩]∙ = {!!}
      ; _[p]∙ = {!!}
      ; true∙ = {!!}
      ; false∙ = {!!}
      ; ite∙ = {!!}
      ; num∙ = {!!}
      ; isZero∙ = {!!}
      ; _+o∙_ = {!!}
      }

  {-
    D : DepModel
    D = record
      ; Var∙ = λ {Γ}{A} _ _ x → ∀{Δ B}(e : Γ ≡ Δ ▹ B){u : Tm Δ B}{Θ}{δ : Sub Θ Δ} → Lift (transp (λ z → Tm z A) e (var x) [ ⟨ u ⟩ ] [ δ ] ≡ transp (λ z → Tm z A) e (var x) [ δ ⁺ ] [ ⟨ u [ δ ] ⟩ ])
      ; vz∙ = λ {Γ}{A}{_}{_}{Δ}{B} e {u}{Θ}{δ} → {!!}
      ; vs∙ = {!!}
      ; Tm∙ = {!!}
      ; Sub∙ = {!!}
      ; p∙ = {!!}
      ; ⟨_⟩∙ = {!!}
      ; _⁺∙ = {!!}
      ; var∙ = {!!}
      ; _[_]∙ = {!!}
      ; [p]∙ = {!!}
      ; vz[⟨⟩]∙ = {!!}
      ; vz[⁺]∙ = {!!}
      ; vs[⟨⟩]∙ = {!!}
      ; vs[⁺]∙ = {!!}
      ; true∙ = {!!}
      ; false∙ = {!!}
      ; ite∙ = {!!}
      ; iteβ₁∙ = {!!}
      ; iteβ₂∙ = {!!}
      ; true[]∙ = {!!}
      ; false[]∙ = {!!}
      ; ite[]∙ = {!!}
      ; num∙ = {!!}
      ; isZero∙ = {!!}
      ; _+o∙_ = {!!}
      ; isZeroβ₁∙ = {!!}
      ; isZeroβ₂∙ = {!!}
      ; +β∙ = {!!}
      ; num[]∙ = {!!}
      ; isZero[]∙ = {!!}
      ; +[]∙ = {!!}
      }
      -}
-}
\end{code}
