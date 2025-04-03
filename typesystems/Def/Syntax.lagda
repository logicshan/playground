\begin{code}
{-# OPTIONS --prop --rewriting #-}
module Def.Syntax where

open import Lib

infixl 6 _[_]
infixl 5 _▹_
infixl 7 _+o_

data Ty   : Set where
  Nat     : Ty
  Bool    : Ty

data Con  : Set where
  ◇       : Con
  _▹_     : Con → Ty → Con

data Var : Con → Ty → Set where
  vz        : ∀{Γ A} → Var (Γ ▹ A) A
  vs        : ∀{Γ A B} → Var Γ A → Var (Γ ▹ B) A

postulate
  Tm        : Con → Ty → Set

data Sub : Con → Con → Set where
  p         : ∀{Γ A} → Sub (Γ ▹ A) Γ
  ⟨_⟩       : ∀{Γ A} → Tm Γ A → Sub Γ (Γ ▹ A)
  _⁺        : ∀{Γ Δ A} → (σ : Sub Δ Γ) → Sub (Δ ▹ A) (Γ ▹ A)

postulate
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

def : {Γ : Con}{A B : Ty} → Tm Γ A → Tm (Γ ▹ A) B → Tm Γ B
def t u = u [ ⟨ t ⟩ ]
{-
DecTy : (A B : Ty) → Prop
DecTy Nat Nat = ⊤
DecTy Nat Bool = ⊥
DecTy Bool Nat = ⊥
DecTy Bool Bool = ⊤

VarConstraint : (Γ : Con)(A : Ty)(n : ℕ) → Prop
VarConstraint ◇ _ _ = ⊥
VarConstraint (Γ ▹ B) A zero = DecTy B A
VarConstraint (Γ ▹ B) A (suc n) = VarConstraint Γ A n
  
private
  v' : (n : ℕ){Γ : Con}{A : Ty}⦃ proof : VarConstraint Γ A n ⦄ → Var Γ A
  v' zero {bc@(_ ▹ _)} {A} ⦃ proof ⦄ = {!  !}
  v' (suc n) {Γ ▹ _} {A} ⦃ proof ⦄ = vs (v' n {Γ} {A} ⦃ proof ⦄)
  
v : (n : ℕ){Γ : Con}{A : Ty}⦃ proof : VarConstraint Γ A n ⦄ → Tm Γ A
v n {Γ} {A} ⦃ x ⦄ = var (v' n {Γ} {A} ⦃ x ⦄)
-}

private
  Var' : ℕ → Con → Ty → Set
  Var' zero Γ A = Var Γ A
  Var' (suc n) Γ A = ∀ {B} → Var' n (Γ ▹ B) A

  Tm' : ℕ → Con → Ty → Set
  Tm' zero Γ A = Tm Γ A
  Tm' (suc n) Γ A = ∀ {B} → Tm' n (Γ ▹ B) A

  vs' : (n : ℕ) {Γ : Con} {A B : Ty} → Var' n Γ A → Var' n (Γ ▹ B) A
  vs' zero x = vs x
  vs' (suc n) x = vs' n x

  var' : (n : ℕ) {Γ : Con} {A : Ty} → Var' n Γ A → Tm' n Γ A
  var' zero x = var x
  var' (suc n) x = var' n x

  v' : (n : ℕ) {Γ : Con} {A : Ty} → Var' n (Γ ▹ A) A
  v' zero = vz
  v' (suc n) = vs' n (v' n)

v : (n : ℕ) {Γ : Con} {A : Ty} → Tm' n (Γ ▹ A) A
v n = var' n (v' n)

v0 : ∀{Γ A} → Tm (Γ ▹ A) A
v0 = var vz
v1 : ∀{Γ A B} → Tm (Γ ▹ A ▹ B) A
v1 = var (vs vz)
v2 : ∀{Γ A B C} → Tm (Γ ▹ A ▹ B ▹ C) A
v2 = var (vs (vs vz))
v3 : ∀{Γ A B C D} → Tm (Γ ▹ A ▹ B ▹ C ▹ D) A
v3 = var (vs (vs (vs vz)))
v4 : ∀{Γ A B C D E} → Tm (Γ ▹ A ▹ B ▹ C ▹ D ▹ E) A
v4 = var (vs (vs (vs (vs vz))))
\end{code}
