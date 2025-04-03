\begin{code}
{-# OPTIONS --prop --rewriting #-}
module Def.ParaModel where

open import Lib
import Def.Syntax as I
open import Def.DepModel

record ParaModel {i j} : Set (lsuc (i ⊔ j)) where
  infixl 6 _[_]∙ _[_]
  infixl 5 _▹∙_ _▹_
  infixl 7 _+o∙_ _+o_

  field
    Ty∙        : Set i
  Ty           : Set i
  Ty           = I.Ty × Ty∙
  field
    Nat∙       : Ty∙
  Nat          : Ty
  Nat          = I.Nat , Nat∙
  field
    Bool∙      : Ty∙
  Bool         : Ty
  Bool         = I.Bool , Bool∙

  field
    Con∙       : Set i
  Con          : Set i
  Con          = I.Con × Con∙
  field
    ◇∙         : Con∙
  ◇            : Con
  ◇            = I.◇ , ◇∙
  field
    _▹∙_       : Con → Ty → Con∙
  _▹_          : Con → Ty → Con
  Γ ▹ A        = π₁ Γ I.▹ π₁ A , Γ ▹∙ A
  
  field
    Var∙       : Con → Ty → Set j
  Var          : Con → Ty → Set j
  Var Γ A      = I.Var (π₁ Γ) (π₁ A) × Var∙ Γ A
  field
    vz∙        : ∀{Γ A} → Var∙ (Γ ▹ A) A
  vz           : ∀{Γ A} → Var (Γ ▹ A) A
  vz           = I.vz , vz∙
  field
    vs∙        : ∀{Γ A B} → Var Γ A → Var∙ (Γ ▹ B) A
  vs           : ∀{Γ A B} → Var Γ A → Var (Γ ▹ B) A
  vs x         = I.vs (π₁ x) , vs∙ x

  field
    Tm∙        : Con → Ty → Set j
  Tm           : Con → Ty → Set j
  Tm Γ A       = I.Tm (π₁ Γ) (π₁ A) × Tm∙ Γ A

  field
    Sub∙       : Con → Con → Set j
  Sub          : Con → Con → Set j
  Sub Δ Γ      = I.Sub (π₁ Δ) (π₁ Γ) × Sub∙ Δ Γ
  field
    p∙         : ∀{Γ A} → Sub∙ (Γ ▹ A) Γ
  p            : ∀{Γ A} → Sub (Γ ▹ A) Γ
  p            = I.p , p∙
  field
    ⟨_⟩∙       : ∀{Γ A} → Tm Γ A → Sub∙ Γ (Γ ▹ A)
  ⟨_⟩          : ∀{Γ A} → Tm Γ A → Sub Γ (Γ ▹ A)
  ⟨ t ⟩        = I.⟨ π₁ t ⟩ , ⟨ t ⟩∙
  field
    _⁺∙        : ∀{Γ Δ A} → (σ : Sub Δ Γ) → Sub∙ (Δ ▹ A) (Γ ▹ A)
  _⁺           : ∀{Γ Δ A} → (σ : Sub Δ Γ) → Sub (Δ ▹ A) (Γ ▹ A)
  σ ⁺          = π₁ σ I.⁺ , σ ⁺∙
  field
    var∙       : ∀{Γ A} → Var Γ A → Tm∙ Γ A
  var          : ∀{Γ A} → Var Γ A → Tm Γ A
  var x        = I.var (π₁ x) , var∙ x
  field
    _[_]∙      : ∀{Γ Δ A} → Tm Γ A → Sub Δ Γ → Tm∙ Δ A
  _[_]         : ∀{Γ Δ A} → Tm Γ A → Sub Δ Γ → Tm Δ A
  a [ γ ]      = π₁ a I.[ π₁ γ ] , a [ γ ]∙
  field
    [p]∙       : ∀{Γ A B x} → π₂ (var {Γ}{A} x [ p {A = B} ]) ≡ π₂ (var (vs x))
    vz[⟨⟩]∙    : ∀{Γ A t} → π₂ (var (vz {Γ}{A}) [ ⟨ t ⟩ ]) ≡ π₂ t
    vz[⁺]∙     : ∀{Γ Δ A σ} → π₂ (var (vz {Γ}{A}) [ σ ⁺ ]) ≡ π₂ (var (vz {Δ}{A}))
    vs[⟨⟩]∙    : ∀{Γ A B x t} → π₂ (var (vs {Γ}{A}{B} x) [ ⟨ t ⟩ ]) ≡ π₂ (var x)
    vs[⁺]∙     : ∀{Γ Δ A B x σ} → π₂ (var (vs {Γ}{A}{B} x) [ σ ⁺ ]) ≡ π₂ (var x [ σ ] [ p {Δ} ])

  field
    true∙      : ∀{Γ} → Tm∙ Γ Bool
  true         : ∀{Γ} → Tm Γ Bool
  true         = I.true , true∙
  field
    false∙     : ∀{Γ} → Tm∙ Γ Bool
  false        : ∀{Γ} → Tm Γ Bool
  false        = I.false , false∙
  field
    ite∙       : ∀{Γ A} → Tm Γ Bool → Tm Γ A → Tm Γ A → Tm∙ Γ A
  ite          : ∀{Γ A} → Tm Γ Bool → Tm Γ A → Tm Γ A → Tm Γ A
  ite t a a'   = I.ite (π₁ t) (π₁ a) (π₁ a') , ite∙ t a a'
  field
    iteβ₁∙     : ∀{Γ A u v} → π₂ (ite {Γ}{A} true u v) ≡ π₂ u
    iteβ₂∙     : ∀{Γ A u v} → π₂ (ite {Γ}{A} false u v) ≡ π₂ v
    true[]∙    : ∀{Γ Δ}{γ : Sub Δ Γ} → π₂ (true [ γ ]) ≡ π₂ (true {Δ})
    false[]∙   : ∀{Γ Δ}{γ : Sub Δ Γ} → π₂ (false [ γ ]) ≡ π₂ (false {Δ})
    ite[]∙     : ∀{Γ A t u v Δ}{γ : Sub Δ Γ} → π₂ ((ite {Γ}{A} t u v) [ γ ]) ≡ π₂ (ite (t [ γ ]) (u [ γ ]) (v [ γ ]))
  
  field
    num∙       : ∀{Γ} → ℕ → Tm∙ Γ Nat
  num          : ∀{Γ} → ℕ → Tm Γ Nat
  num n        = I.num n , num∙ n
  field
    isZero∙    : ∀{Γ} → Tm Γ Nat → Tm∙ Γ Bool
  isZero       : ∀{Γ} → Tm Γ Nat → Tm Γ Bool
  isZero t     = I.isZero (π₁ t) , isZero∙ t
  field
    _+o∙_      : ∀{Γ} → Tm Γ Nat → Tm Γ Nat → Tm∙ Γ Nat
  _+o_         : ∀{Γ} → Tm Γ Nat → Tm Γ Nat → Tm Γ Nat
  t +o t'      = π₁ t I.+o π₁ t' , t +o∙ t'
  field
    isZeroβ₁∙  : ∀{Γ} → π₂ (isZero (num {Γ} 0)) ≡ π₂ (true {Γ})
    isZeroβ₂∙  : ∀{Γ n} → π₂ (isZero (num {Γ} (1 + n))) ≡ π₂ (false {Γ})
    +β∙        : ∀{Γ m n} → π₂ (num {Γ} m +o num n) ≡ π₂ (num (m + n))

    num[]∙     : ∀{Γ n Δ}{γ : Sub Δ Γ} → π₂ (num n [ γ ]) ≡ π₂ (num n)
    isZero[]∙  : ∀{Γ t Δ}{γ : Sub Δ Γ} → π₂ (isZero t [ γ ]) ≡ π₂ (isZero (t [ γ ]))
    +[]∙       : ∀{Γ u v Δ}{γ : Sub Δ Γ} → π₂ ((u +o v) [ γ ]) ≡ π₂ ((u [ γ ]) +o (v [ γ ]))

  D : DepModel {i} {j} -- we use Γ instead of I.Γ for metavariables
  D = record
    { Ty∙       = λ _ → Ty∙
    ; Nat∙      = Nat∙
    ; Bool∙     = Bool∙
    ; Con∙      = λ _ → Con∙
    ; ◇∙        = ◇∙
    ; _▹∙_      = λ {Γ}{A} Γ∙ A∙ → (Γ , Γ∙) ▹∙ (A , A∙)
    ; Var∙      = λ {Γ}{A} Γ∙ A∙ _ → Var∙ (Γ , Γ∙) (A , A∙)
    ; vz∙       = vz∙
    ; vs∙       = λ where {x = x} x∙ → vs∙ (x , x∙) 
    ; Tm∙       = λ {Γ}{A} Γ∙ A∙ _ → Tm∙ (Γ , Γ∙) (A , A∙)
    ; Sub∙      = λ {Δ}{Γ} Δ∙ Γ∙ _ → Sub∙ (Δ , Δ∙) (Γ , Γ∙)
    ; p∙        = p∙
    ; ⟨_⟩∙      = λ where {t = t} t∙ → ⟨ t , t∙ ⟩∙
    ; _⁺∙       = λ where {σ = σ} σ∙ → (σ , σ∙) ⁺∙
    ; var∙      = λ where {x = x} x∙ → var∙ (x , x∙)
    ; _[_]∙     = λ where {t = t}{σ = σ} t∙ σ∙ → (t , t∙) [ σ , σ∙ ]∙
    ; [p]∙      = [p]∙
    ; vz[⟨⟩]∙   = vz[⟨⟩]∙
    ; vz[⁺]∙    = vz[⁺]∙
    ; vs[⟨⟩]∙   = vs[⟨⟩]∙
    ; vs[⁺]∙    = vs[⁺]∙
    ; true∙     = true∙
    ; false∙    = false∙
    ; ite∙      = λ where {t = t}{u = u}{v = v} t∙ u∙ v∙ → ite∙ (t , t∙) (u , u∙) (v , v∙)
    ; iteβ₁∙    = iteβ₁∙
    ; iteβ₂∙    = iteβ₂∙
    ; true[]∙   = true[]∙
    ; false[]∙  = false[]∙
    ; ite[]∙    = ite[]∙
    ; num∙      = num∙
    ; isZero∙   = λ where {t = t} t∙ → isZero∙ (t , t∙)
    ; _+o∙_     = λ where {u = u}{v = v} u∙ v∙ → (u , u∙) +o∙ (v , v∙)
    ; isZeroβ₁∙ = isZeroβ₁∙
    ; isZeroβ₂∙ = isZeroβ₂∙
    ; +β∙       = +β∙
    ; num[]∙    = num[]∙
    ; isZero[]∙ = isZero[]∙
    ; +[]∙      = +[]∙
    }
  module D = DepModel D

  ⟦_⟧T : I.Ty → Ty∙
  ⟦_⟧T = D.⟦_⟧T

  ⟦_⟧C : I.Con → Con∙
  ⟦_⟧C = D.⟦_⟧C

  ⟦_⟧v : ∀{Γ A} → I.Var Γ A → Var∙ (Γ , ⟦ Γ ⟧C) (A , ⟦ A ⟧T)
  ⟦_⟧v = D.⟦_⟧v

  ⟦_⟧t : ∀{Γ A} → I.Tm Γ A  → Tm∙  (Γ , ⟦ Γ ⟧C) (A , ⟦ A ⟧T)
  ⟦_⟧t = D.⟦_⟧t

  ⟦_⟧s : ∀{Δ Γ} → I.Sub Δ Γ → Sub∙ (Δ , ⟦ Δ ⟧C) (Γ , ⟦ Γ ⟧C)
  ⟦_⟧s = D.⟦_⟧s
\end{code}
