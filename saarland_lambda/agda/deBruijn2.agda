module deBruijn2 where

open import Data.Nat.Base using (ℕ; zero; suc)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)

infix  5 ƛ_
infixl 7 _·_
infix  9 `_
infixr 4 _∙_

infixl 10 _∘_
infixr  20 ⇑_

data Ter : Set where
  `_   : ℕ → Ter
  _·_  : Ter → Ter → Ter
  ƛ_   : Ter → Ter

-- substitution type
Sub : Set
Sub = ℕ → Ter

-- identity substitution
I : Sub
I = λ n → ` n

-- successor substitution
S : Sub
S = λ n → ` suc n

-- cons operation
_∙_ : {A : Set} → A → (ℕ → A) → (ℕ → A)
s ∙ σ = λ { zero    → s
          ; (suc n) → σ n
          }
_⊚_ : {A B C : Set} → (f : A → B) → (g : B → C) → A → C
f ⊚ g = λ x → g (f x)

Rename : Set
Rename = ℕ → ℕ

upr : Rename → Rename
upr ξ = zero ∙ (ξ ⊚ suc)

ren : Rename → Sub
ren ξ = λ x → ` (ξ x)

_⟨_⟩ : Ter → Rename → Ter
(` n)   ⟨ ξ ⟩ = ` ξ n
(s · t) ⟨ ξ ⟩ = s ⟨ ξ ⟩ · t ⟨ ξ ⟩
(ƛ s)   ⟨ ξ ⟩ = ƛ (s ⟨ upr ξ ⟩)

rename : Rename → Ter → Ter
rename ξ s = s ⟨ ξ ⟩

-- up
⇑_ : Sub → Sub
⇑ σ = ` zero ∙ (σ ⊚ rename suc)

-- instantiation operation
_[_] : Ter → Sub → Ter
(` n)   [ σ ] = σ n
(s · t) [ σ ] = (s [ σ ]) · (t [ σ ])
(ƛ s)   [ σ ] = ƛ (s [ ⇑ σ ])

inst : Sub → Ter → Ter
inst σ s = s [ σ ]

-- composition
_∘_ : Sub → Sub → Sub
σ ∘ τ = λ n → (σ n) [ τ ]

β : Ter → Ter → Ter
β s t = s [ t ∙ I ]

postulate
  funext : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

fact3 : (⇑ I) ≡ I
fact3 = funext lemma
  where
  lemma : (n : ℕ) → (⇑ I) n ≡ I n
  lemma zero    = refl
  lemma (suc n) = refl


fact4 : (s : Ter) → s [ I ] ≡ s
fact4 (` n)                             = refl
fact4 (s · t) rewrite fact4 s | fact4 t = refl
fact4 (ƛ s)   rewrite fact3   | fact4 s = refl

-- Renaming is a special case of institution

upr_up : (ξ : Rename) → ren (upr ξ) ≡ ⇑ (ren ξ)
upr_up ξ = funext lemma
  where
  lemma : (n : ℕ) → ren (upr ξ) n ≡ (⇑ ren ξ) n
  lemma zero = refl
  lemma (suc n) = refl

rename_inst : (ξ : Rename) → rename ξ ≡ inst (ren ξ)
rename_inst ξ = funext (lemma ξ)
  where
  lemma : (ξ : Rename) → (s : Ter) → rename ξ s ≡ inst (ren ξ) s
  lemma ξ (` x) = refl
  lemma ξ (s · t) rewrite lemma ξ s | lemma ξ t = refl
  lemma ξ (ƛ s) rewrite lemma (upr ξ) s | sym (upr_up ξ) = refl

fact5-1 :(τ : Sub) → S ∘ ⇑ τ ≡ τ ∘ S
fact5-1 τ = funext lemma
  where
  lemma : (x : ℕ) → (S ∘ ⇑ τ) x ≡ (τ ∘ S) x
  lemma n rewrite cong (λ f → f (τ n)) (rename_inst suc) = refl
