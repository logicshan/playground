\begin{code}
{-# OPTIONS --prop --rewriting #-}
module Def.Model where

open import Lib
import Def.Syntax as I
open import Def.DepModel

record Model {i j} : Set (lsuc (i ⊔ j)) where
  infixl 6 _[_]
  infixl 5 _▹_
  infixl 7 _+o_

  field
    Ty        : Set i
    Nat       : Ty
    Bool      : Ty

    Con       : Set i
    ◇         : Con
    _▹_       : Con → Ty → Con

    Var       : Con → Ty → Set j
    vz        : ∀{Γ A} → Var (Γ ▹ A) A
    vs        : ∀{Γ A B} → Var Γ A → Var (Γ ▹ B) A

    Tm        : Con → Ty → Set j

    Sub       : Con → Con → Set j
    p         : ∀{Γ A} → Sub (Γ ▹ A) Γ
    ⟨_⟩       : ∀{Γ A} → Tm Γ A → Sub Γ (Γ ▹ A)
    _⁺        : ∀{Γ Δ A} → (σ : Sub Δ Γ) → Sub (Δ ▹ A) (Γ ▹ A)

    var       : ∀{Γ A} → Var Γ A → Tm Γ A
    _[_]      : ∀{Γ Δ A} → Tm Γ A → Sub Δ Γ → Tm Δ A
    [p]       : ∀{Γ A B x} → var {Γ}{A} x [ p {A = B} ] ≡ var (vs x)
    vz[⟨⟩]    : ∀{Γ A t} → var (vz {Γ}{A}) [ ⟨ t ⟩ ] ≡ t
    vz[⁺]     : ∀{Γ Δ A σ} → var (vz {Γ}{A}) [ σ ⁺ ] ≡ var (vz {Δ}{A})
    vs[⟨⟩]    : ∀{Γ A B x t} → var (vs {Γ}{A}{B} x) [ ⟨ t ⟩ ] ≡ var x
    vs[⁺]     : ∀{Γ Δ A B x σ} → var (vs {Γ}{A}{B} x) [ σ ⁺ ] ≡ var x [ σ ] [ p {Δ} ]

    true      : ∀{Γ} → Tm Γ Bool
    false     : ∀{Γ} → Tm Γ Bool
    ite       : ∀{Γ A} → Tm Γ Bool → Tm Γ A → Tm Γ A → Tm Γ A
    iteβ₁     : ∀{Γ A u v} → ite {Γ}{A} true  u v ≡ u
    iteβ₂     : ∀{Γ A u v} → ite {Γ}{A} false u v ≡ v
    true[]    : ∀{Γ Δ σ} → true  {Γ} [ σ ] ≡ true  {Δ}
    false[]   : ∀{Γ Δ σ} → false {Γ} [ σ ] ≡ false {Δ}
    ite[]     : ∀{Γ Δ A t u v σ} → (ite {Γ}{A} t u v) [ σ ] ≡ ite {Δ} (t [ σ ]) (u [ σ ]) (v [ σ ])
    
    num       : ∀{Γ} → ℕ → Tm Γ Nat
    isZero    : ∀{Γ} → Tm Γ Nat → Tm Γ Bool
    _+o_      : ∀{Γ} → Tm Γ Nat → Tm Γ Nat → Tm Γ Nat
    isZeroβ₁  : ∀{Γ} → isZero (num 0) ≡ true {Γ = Γ}
    isZeroβ₂  : ∀{Γ n} → isZero (num (1 + n)) ≡ false {Γ = Γ}
    +β        : ∀{Γ m n} → num m +o num n ≡ num {Γ = Γ} (m + n)
    num[]     : ∀{Γ Δ σ n} → num {Γ} n [ σ ] ≡ num {Δ} n
    isZero[]  : ∀{Γ Δ t σ} → (isZero {Γ} t) [ σ ] ≡ isZero {Δ} (t [ σ ])
    +[]       : ∀{Γ Δ u v}{σ : Sub Δ Γ} → (u +o v) [ σ ] ≡ (u [ σ ]) +o (v [ σ ])

  def : ∀{Γ A B} → Tm Γ A → Tm (Γ ▹ A) B → Tm Γ B
  def u t = t [ ⟨ u ⟩ ]

  D : DepModel
  D = record
    { Ty∙ = λ _ → Ty
    ; Nat∙ = Nat
    ; Bool∙ = Bool
    ; Con∙ = λ _ → Con
    ; ◇∙ = ◇
    ; _▹∙_ = _▹_
    ; Var∙ = λ Γ A _ → Var Γ A
    ; vz∙ = vz
    ; vs∙ = vs
    ; Tm∙ = λ Γ A _ → Tm Γ A
    ; Sub∙ = λ Δ Γ _ → Sub Δ Γ
    ; p∙ = p
    ; ⟨_⟩∙ = ⟨_⟩
    ; _⁺∙ = _⁺
    ; var∙ = var
    ; _[_]∙ = _[_]
    ; [p]∙ = [p]
    ; vz[⟨⟩]∙ = λ {Γ}{A}{t} → vz[⟨⟩]
    ; vz[⁺]∙ = vz[⁺]
    ; vs[⟨⟩]∙ = vs[⟨⟩]
    ; vs[⁺]∙ = λ {Γ}{Δ}{A}{B}{x}{σ} → vs[⁺]
    ; true∙ = true
    ; false∙ = false
    ; ite∙ = ite
    ; iteβ₁∙ = λ {Γ}{A}{u}{v} → iteβ₁
    ; iteβ₂∙ = λ {Γ}{A}{u}{v} → iteβ₂
    ; true[]∙ = true[]
    ; false[]∙ = false[]
    ; ite[]∙ = ite[]
    ; num∙ = num
    ; isZero∙ = isZero
    ; _+o∙_ = _+o_
    ; isZeroβ₁∙ = isZeroβ₁
    ; isZeroβ₂∙ = isZeroβ₂
    ; +β∙ = +β
    ; num[]∙ = num[]
    ; isZero[]∙ = isZero[]
    ; +[]∙ = +[]
    }
  module D = DepModel D

  ⟦_⟧T : I.Ty → Ty
  ⟦_⟧T = D.⟦_⟧T

  ⟦_⟧C : I.Con → Con
  ⟦_⟧C = D.⟦_⟧C

  ⟦_⟧v : ∀{Γ A} → I.Var Γ A → Var ⟦ Γ ⟧C ⟦ A ⟧T
  ⟦_⟧v = D.⟦_⟧v

  ⟦_⟧t : ∀{Γ A} → I.Tm Γ A  → Tm  ⟦ Γ ⟧C ⟦ A ⟧T
  ⟦_⟧t = D.⟦_⟧t

  ⟦_⟧s : ∀{Δ Γ} → I.Sub Δ Γ → Sub ⟦ Δ ⟧C  ⟦ Γ ⟧C
  ⟦_⟧s = D.⟦_⟧s
\end{code}
