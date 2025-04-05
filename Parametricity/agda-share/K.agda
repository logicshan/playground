{-# OPTIONS --without-K #-}

module K where

data ⊥ : Set where

⊥-elim : ∀{A : Set} → ⊥ → A
⊥-elim ()

¬_ : Set → Set
¬ A = A → ⊥

data Dec (P : Set) : Set where
  yes :   P → Dec P
  no  : ¬ P → Dec P

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

J : ∀{A} {x : A} (P : (y : A) → x ≡ y → Set) {y : A} (eq : x ≡ y) → P x refl → P y eq
J P refl Pxr = Pxr

infixl 70 _⁻¹
_⁻¹ : ∀{A} {x y : A} → x ≡ y → y ≡ x
eq ⁻¹ = J (λ w _ → w ≡ _) eq refl

infixl 20 _∘_
_∘_ : ∀{A} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
xy ∘ yz = J (λ w _ → _ ≡ w) yz xy

map : ∀{A B} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
map f eq = J (λ w _ → f _ ≡ f w) eq refl

inv : ∀{A} {x y : A} (eq : x ≡ y) → eq ∘ eq ⁻¹ ≡ refl
inv eq = J (λ w xw → xw ∘ xw ⁻¹ ≡ refl) eq refl

KP : Set → Set₁
KP A = (x : A) → (P : x ≡ x → Set) → (eq : x ≡ x) → P refl → P eq

module Decidable (A : Set) (dec : ∀(x y : A) → Dec (x ≡ y)) where
  f : ∀{x y} → x ≡ y → x ≡ y
  f {x} {y} p with dec x y
  ... | yes r = r
  ... | no  k = ⊥-elim (k p)

  g : ∀{x y} → x ≡ y → x ≡ y
  g eq = eq ∘ f refl ⁻¹

  lemma₀ : ∀{x y} (p : x ≡ y) → g (f p) ≡ p
  lemma₀ p = J (λ w xw → g (f xw) ≡ xw) p (inv (f refl)) -- f refl ∘ f refl ⁻¹ ≡ refl

  lemma₁ : ∀{x y} (p q : x ≡ y) → f p ≡ f q
  lemma₁ {x} {y} p q with dec x y
  ... | yes _ = refl
  ... | no  k = ⊥-elim (k p)

  lemma₂ : ∀{x y} (p q : x ≡ y) → p ≡ q
  lemma₂ p q = lemma₀ p ⁻¹ ∘ map g (lemma₁ p q) ∘ lemma₀ q

  K : ∀{x : A} (P : x ≡ x → Set) → (eq : x ≡ x) → P refl → P eq
  K P eq = J (λ q _ → P q) (lemma₂ refl eq)


  

