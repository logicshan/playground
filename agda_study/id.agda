data _≡₁_ {A : Set} (a : A) : A → Set where
  refl₁ : a ≡₁ a

data _≡₂_ {A : Set} {a : A} : A → A → Set where
  refl₂ : a ≡₂ a
