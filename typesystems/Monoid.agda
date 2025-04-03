{-# OPTIONS --prop --rewriting #-}

module Monoid {ℓ} (A : Set ℓ) where

  open import Lib hiding (_∘_)

  module I where
    postulate
      C : Set ℓ
      f : A → C
      _∘_ : C → C → C
      id : C
      ass : ∀ {a b c} → (a ∘ b) ∘ c ≡ a ∘ (b ∘ c)
      idl : ∀ {a} → id ∘ a ≡ a
      idr : ∀ {a} → a ∘ id ≡ a

  record Model : Set (lsuc ℓ) where
    field
      C : Set ℓ
      f : A → C
      _∘_ : C → C → C
      id : C
      ass : ∀ {a b c} → (a ∘ b) ∘ c ≡ a ∘ (b ∘ c)
      idl : ∀ {a} → id ∘ a ≡ a
      idr : ∀ {a} → a ∘ id ≡ a

    postulate
      ⟦_⟧ : I.C → C
      ⟦f⟧ : ∀ {a : A} → ⟦ I.f a ⟧ ≈ f a
      ⟦∘⟧ : ∀ {c₁ c₂ : I.C} → ⟦ c₁ I.∘ c₂ ⟧ ≈ ⟦ c₁ ⟧ ∘ ⟦ c₂ ⟧
      ⟦id⟧ : ⟦ I.id ⟧ ≈ id
      {-# REWRITE ⟦f⟧ ⟦∘⟧ ⟦id⟧ #-}


  infixr 5 _∷_
  data List {ℓ} (A : Set ℓ) : Set ℓ where
    []  : List A
    _∷_ : (x : A) (xs : List A) → List A

  infixr 5 _++_
  _++_ : List A → List A → List A
  []       ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  ++-assoc : {xs ys zs : List A} → ((xs ++ ys) ++ zs) ≡ (xs ++ (ys ++ zs))
  ++-assoc {[]} {ys} {zs} = refl
  ++-assoc {x ∷ xs} {ys} {zs} = cong (x ∷_) (++-assoc {xs} {ys} {zs})

  ++-identityʳ : {xs : List A} → xs ++ [] ≡ xs
  ++-identityʳ {[]}       = refl
  ++-identityʳ {x ∷ xs} = cong (x ∷_) (++-identityʳ {xs})

  Nf : Set ℓ
  Nf = List A

  N : Model
  N = record
       { C = Nf
       ; f = _∷ []
       ; _∘_ = _++_
       ; id = []
       ; ass = λ {a} {b} {c} → ++-assoc {a} {b} {c}
       ; idl = refl
       ; idr = ++-identityʳ
       }

  module N = Model N

  norm : I.C → Nf
  norm = N.⟦_⟧

  ⌜_⌝ : Nf → I.C
  ⌜ [] ⌝ = I.id
  ⌜ x ∷ xs ⌝ = I.f x I.∘ ⌜ xs ⌝

  stab : (v : Nf) → norm ⌜ v ⌝ ≡ v
  stab [] = refl
  stab (x ∷ v) = cong (x ∷_) (stab v)

  record DepModel : Set (lsuc ℓ) where
    field
      C∙ : I.C → Set ℓ
      f∙ : ∀ {a} → C∙ (I.f a)
      _∘∙_ : ∀ {a b} → C∙ a → C∙ b → C∙ (a I.∘ b)
      id∙ : C∙ I.id
      ass∙ : ∀ {a b c} → (a∙ : C∙ a) → (b∙ : C∙ b) → (c∙ : C∙ c)
             → (C∙ ~) I.ass ((id∙ ∘∙ c∙) ∘∙ c∙) (id∙ ∘∙ (c∙ ∘∙ c∙))
      idl∙ : ∀ {a} → (a∙ : C∙ a) → (C∙ ~) I.idl (id∙ ∘∙ a∙) a∙
      idr∙ : ∀ {a} → (a∙ : C∙ a) → (C∙ ~) I.idr (a∙ ∘∙ id∙) a∙
    postulate
      ⟦_⟧ : (a : I.C) → C∙ a
      ⟦f⟧ : ∀ {a} → ⟦ I.f a ⟧ ≈ f∙
      ⟦∘⟧ : ∀ {a b} → ⟦ a I.∘ b ⟧ ≈ ⟦ a ⟧ ∘∙ ⟦ b ⟧
      ⟦id⟧ : ⟦ I.id ⟧ ≈ id∙
      {-# REWRITE ⟦f⟧ ⟦id⟧ #-}

  sym : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → y ≡ x
  sym refl = refl

  ⌜++⌝ : ∀ {xs ys} → ⌜ xs ++ ys ⌝ ≡ ⌜ xs ⌝ I.∘ ⌜ ys ⌝
  ⌜++⌝ {[]} {ys} = sym I.idl
  ⌜++⌝ {x ∷ xs} {ys} = cong (I.f x I.∘_) (⌜++⌝ {xs} {ys}) ◾ sym I.ass

  Comp : DepModel
  Comp = record
          { C∙ = λ x → Lift (⌜ norm x ⌝ ≡ x)
          ; f∙ = mk I.idr
          ; _∘∙_ = λ{ (mk p) (mk q) → mk (⌜++⌝ ◾ (cong₂ I._∘_ p q)) }
          ; id∙ = mk refl
          ; ass∙ = λ _ _ _ → refl
          ; idl∙ = λ _ → refl
          ; idr∙ = λ _ → refl
          }
  module Comp = DepModel Comp

  comp : (x : I.C) → ⌜ norm x ⌝ ≡ x
  comp x = un (Comp.⟦ x ⟧)
