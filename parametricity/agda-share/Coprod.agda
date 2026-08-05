{-# OPTIONS --without-K #-}

module Coprod where

-- Some utilities
id : ∀{A : Set} → A → A
id x = x

_∘_ : ∀{A B C : Set} → (B → C) → (A → B) → (A → C)
g ∘ f = λ x → g (f x)

const : ∀{A B : Set} → A → B → A
const x _ = x

-- The empty type, small and large elimination
data ⊥ : Set where

⊥-elim : ∀{A : Set} → ⊥ → A
⊥-elim ()

⊥-Elim : ⊥ → Set
⊥-Elim ()

-- The singleton type
record ⊤ : Set where

-- Coproducts
data _+_ (A B : Set) : Set where
  inl : A → A + B
  inr : B → A + B

-- Small elimination
+-elim : {A B : Set} (P : A + B → Set)
       → ((x : A) → P (inl x)) 
       → ((y : B) → P (inr y))
       → (s : A + B) → P s
+-elim P f _ (inl x) = f x
+-elim P _ g (inr y) = g y

-- Large elimination
+-Elim : {A B : Set} → (A → Set) → (B → Set) → A + B → Set
+-Elim F _ (inl x) = F x
+-Elim _ G (inr y) = G y

-- A second kind of large elimination. I found myself needing this,
-- and I don't think it's possible to write using only the above
-- large elimination.
+-Elim₂ : {A B : Set} (P : A + B → Set)
        → ((x : A) → P (inl x) → Set)
        → ((y : B) → P (inr y) → Set)
        → (s : A + B) → P s → Set
+-Elim₂ P F _ (inl x) plx = F x plx
+-Elim₂ P _ G (inr y) pry = G y pry

_-+-_ : ∀{A B C : Set} → (A → C) → (B → C) → A + B → C
f -+- g = +-elim _ f g

-- Dependent sums
record Σ (A : Set) (T : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : T proj₁

infixr 40 _,_
open Σ

syntax Σ A (λ x → T) = Σ[ x ∶ A ] T

-- Equality/paths
data _⟿_ {A : Set} (x : A) : A → Set where
  refl : x ⟿ x

J : {A : Set} {x : A} (P : (y : A) → x ⟿ y → Set)
  → {y : A} → (eq : x ⟿ y) → P x refl → P y eq
J P refl Pxr = Pxr

subst : ∀{A : Set} (P : A → Set) {x y : A} → x ⟿ y → P x → P y
subst P eq = J (λ z _ → P z) eq

sym : ∀{A : Set} {x y : A} → x ⟿ y → y ⟿ x
sym {A} {x} eq = subst (λ z → z ⟿ x) eq refl

cong : ∀{A B : Set} (f : A → B) {x y : A} → x ⟿ y → f x ⟿ f y
cong f eq = subst (λ z → f _ ⟿ f z) eq refl

infixr 20 _◎_
_◎_ : ∀{A : Set} → {x y z : A} → x ⟿ y → y ⟿ z → x ⟿ z
eq₁ ◎ eq₂ = subst (λ z → _ ⟿ z) eq₂ eq₁

◎-identˡ : ∀{A : Set} {x y : A} → (eq : x ⟿ y) → refl ◎ eq ⟿ eq
◎-identˡ eq = J (λ z eq' → refl ◎ eq' ⟿ eq') eq refl

◎-identʳ : ∀{A : Set} {x y : A} → (eq : x ⟿ y) → eq ◎ refl ⟿ eq
◎-identʳ eq = refl

-- Alternate definition of equivalence thanks to Peter LeFanu Lumsdaine
RightHInv : ∀{A B : Set} → (f : A → B) → Set
RightHInv {A} {B} f = Σ[ g ∶ (B → A) ] (∀ y → g (f y) ⟿ y)

LeftHInv : ∀{A B : Set} → (f : A → B) → Set
LeftHInv {A} {B} f = Σ[ g ∶ (B → A) ] (∀ y → f (g y) ⟿ y)

IsEquiv : ∀{A B : Set} → (f : A → B) → Set
IsEquiv f = Σ (LeftHInv f) (\_ → RightHInv f)

-- A quick detour. The pullback of the coproduct constructors is
-- empty.
module Intersection (A B X : Set)
                    (f : X → A) (g : X → B)
                    (eq : ∀ x → inl (f x) ⟿ inr (g x)) where

  ! : X → ⊥
  ! x = J P (eq x) _
   where
   P : (s : A + B) → inl (f x) ⟿ s → Set
   P s eq = +-Elim (λ _ → ⊤) (λ _ → ⊥) s

  comm₁ : ∀ x → ⊥-elim (! x) ⟿ f x
  comm₁ x = ⊥-elim (! x)

  comm₂ : ∀ x → ⊥-elim (! x) ⟿ g x
  comm₂ x = ⊥-elim (! x)

  uniq : ∀(!! : X → ⊥) x → !! x ⟿ ! x
  uniq !! x = ⊥-elim (!! x)

module inl-Monic {A B : Set} (x : A) where
  P₁ : (s : A + B) → inl x ⟿ s → Set
  P₁ z eq = x ⟿ +-elim (λ _ → A) id (const x) z

  -- We can peel off inls
  outl : ∀ y → _⟿_ {A + B} (inl x) (inl y) → x ⟿ y
  outl y eq = J P₁ eq refl

  inv₁ : ∀ y → (eq : x ⟿ y) → outl y (cong inl eq) ⟿ eq
  inv₁ y eq = J (λ z eq' → outl z (cong inl eq') ⟿ eq') eq refl

  -- Perhaps there's a better way to prove this half of the equivalence,
  -- but I haven't found one. I was going to switch to a Martin-löf style
  -- universe for this, but I realized I could then only define P₂ for
  -- A, B : U, which isn't good enough.
  P₂ : (s : A + B) → inl x ⟿ s → Set
  P₂ = +-Elim₂ (λ s → inl x ⟿ s)
               (λ z eq' → cong inl (outl z eq') ⟿ eq')
               (λ y eq' → ⊥-Elim
                 (Intersection.! A B ⊤ (const x) (const y) (const eq') _))

  inv₂ : ∀ y → (eq : inl x ⟿ inl y) → cong inl (outl y eq) ⟿ eq
  inv₂ y eq = J P₂ eq refl

  -- So, the obvious 'cong inl : x ⟿ y → inl x ⟿ inl y' is an equivalence
  equiv : ∀ y → IsEquiv {x ⟿ y} {inl {A} {B} x ⟿ inl y} (cong inl)
  equiv y = (outl y , inv₂ y) , (outl y , inv₁ y)

-- inr monic follows from a similar argument

-- Thus, coproducts are disjoint (functional extensionality has
-- been expanded into the above lemmas, because they won't hold
-- intensionally).

record _×_ {A B Z : Set} (f : A → Z) (g : B → Z) : Set where
  constructor _,_⟨_⟩
  field
    fst : A
    snd : B
    φ : f fst ⟿ g snd

open _×_

lemma₁ : ∀{A B} → (x : A + B)
       → (Σ[ a ∶ A ] (x ⟿ inl a)) + (Σ[ b ∶ B ] (x ⟿ inr b))
lemma₁ x = +-elim P (λ a → inl (a , refl)) (λ b → inr (b , refl)) x
 where
 P : _ → Set
 P z = (Σ _ \a → z ⟿ inl a) + (Σ _ \b → z ⟿ inr b)

-- I stared at the 2-pullback definition to write this module, but it's
-- apparently wrong. It took so much work, though, I hate to delete it.
module Is2Pullback (A B C X : Set)
                   (f : A → C) (g : B → C)
                   (m : X → A) (n : X → B)
                   (ψ : ∀ x → f (m x) ⟿ g (n x)) where
  h : X → f × g
  h x = m x , n x ⟨ ψ x ⟩

  α : ∀ x → fst (h x) ⟿ m x
  α x = refl

  β : ∀ x → snd (h x) ⟿ n x
  β x = refl

  κ : ∀ x → φ (h x) ⟿ ψ x
  κ x = refl

  ×-eta-φ : (x : A) (y : B) → (φ₁ φ₂ : f x ⟿ g y) → φ₁ ⟿ φ₂
          → _⟿_ {f × g} (x , y ⟨ φ₁ ⟩) (x , y ⟨ φ₂ ⟩)
  ×-eta-φ x y φ₁ φ₂ eq = subst (λ p → (x , y ⟨ φ₁ ⟩) ⟿ (x , y ⟨ p ⟩)) eq refl

  ×-eta : (x₁ x₂ : A) (y₁ y₂ : B) (φ₁ : f x₁ ⟿ g y₁) (φ₂ : f x₂ ⟿ g y₂)
        → (eq₁ : x₁ ⟿ x₂) → (eq₂ : y₁ ⟿ y₂)
        → (coh : φ₁ ◎ cong g eq₂ ⟿ cong f eq₁ ◎ φ₂)
        → _⟿_ {f × g} (x₁ , y₁ ⟨ φ₁ ⟩) (x₂ , y₂ ⟨ φ₂ ⟩)
  ×-eta x₁ x₂ y₁ y₂ φ₁ φ₂ eq₁ eq₂ coh =
     J P₁ eq₁ (J P₂ eq₂ (λ θ₂ coh'
                         → ×-eta-φ x₁ y₁ φ₁ θ₂ (coh' ◎ ◎-identˡ θ₂))) φ₂ coh
   where
   P₁ : ∀ z → x₁ ⟿ z → Set
   P₁ z eq' = (θ : f z ⟿ g y₂) → φ₁ ◎ cong g eq₂ ⟿ cong f eq' ◎ θ
            → _⟿_ {f × g} (x₁ , y₁ ⟨ φ₁ ⟩) (z , y₂ ⟨ θ ⟩)

   P₂ : ∀ w → y₁ ⟿ w → Set
   P₂ w eq' = (θ : f x₁ ⟿ g w) → φ₁ ◎ cong g eq' ⟿ refl ◎ θ
            → _⟿_ {f × g} (x₁ , y₁ ⟨ φ₁ ⟩) (x₁ , w ⟨ θ ⟩)

  module Unique (k : X → f × g)
                (μ : ∀ x → fst (h x) ⟿ fst (k x))
                (ν : ∀ x → snd (h x) ⟿ snd (k x))
                (χ : ∀ x → (φ (h x) ◎ cong g (ν x)) ⟿ (cong f (μ x) ◎ φ (k x)))
    where
    γ : ∀ x → h x ⟿ k x
    γ x = ×-eta (fst (h x)) (fst (k x))
                (snd (h x)) (snd (k x))
                (φ (h x))   (φ (k x)) 
                (μ x) (ν x) (χ x)

-- Mike Shulman suggests this is the proper definition of homotopy pullback.
-- Remarkably, it was much easier to prove (thanks, eta).
module IsHPullback (A B C X : Set)
                   (f : A → C) (g : B → C) where
   T : Set
   T = Σ[ m ∶ (X → A) ] (Σ[ n ∶ (X → B) ] (∀ x → f (m x) ⟿ g (n x)))

   θ : (X → f × g) → T
   θ h = ((fst ∘ h) , (snd ∘ h) , λ x → φ (h x))

   θ⁻¹ : T → (X → f × g)
   θ⁻¹ t x = proj₁ t x , proj₁ (proj₂ t) x ⟨ proj₂ (proj₂ t) x ⟩

   equiv : IsEquiv θ
   equiv = (θ⁻¹ , λ y → refl) , (θ⁻¹ , λ h → refl)

module Stable (A B C D : Set)
              (f : A → D) (g : B → D) (h : C → D) where
  factor : (f × g) + (f × h) → f × (g -+- h)
  factor = +-elim _ (λ v → fst v , inl (snd v) ⟨ φ v ⟩)
                    (λ v → fst v , inr (snd v) ⟨ φ v ⟩)

  P₁ : f × (g -+- h) → B + C → Set
  P₁ v s = f (fst v) ⟿ (g -+- h) s → (f × g) + (f × h)

  distrib : f × (g -+- h) → (f × g) + (f × h)
  distrib v = +-elim (P₁ v) (λ b eq → inl (fst v , b ⟨ eq ⟩))
                            (λ c eq → inr (fst v , c ⟨ eq ⟩)) (snd v) (φ v)

  P₂ : f × (g -+- h) → B + C → Set
  P₂ v s = (eq : f (fst v) ⟿ (g -+- h) s)
         → factor (distrib (fst v , s ⟨ eq ⟩)) ⟿ (fst v , s ⟨ eq ⟩)

  inv₁ : ∀ v → factor (distrib v) ⟿ v
  inv₁ v = +-elim (P₂ v) (λ x eq → refl) (λ y eq → refl) (snd v) (φ v)

  inv₂ : ∀ v → distrib (factor v) ⟿ v
  inv₂ = +-elim (λ v → distrib (factor v) ⟿ v) (λ x → refl) (λ y → refl)

  equiv : IsEquiv factor
  equiv = (distrib , inv₁) , (distrib , inv₂)
